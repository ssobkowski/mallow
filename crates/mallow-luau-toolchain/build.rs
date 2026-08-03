//! Generate the typed, zero-runtime-cost registry from `registry.json`.
//!
//! This build script deliberately keeps validation here (rather than in the
//! downloader) so a malformed registry can never make it into a release build.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::marker::PhantomData;
use std::path::Path;
use std::{env, fs};

use serde::de::{Error as _, MapAccess, Visitor};
use serde::{Deserialize, Deserializer};

/// Registry schema accepted by this build script.
const SCHEMA: u32 = 1;

/// Deserialized top-level registry document.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RegistryFile {
    /// Canonical schema number.
    schema: u32,
    /// Releases keyed by their exact upstream tag.
    #[serde(deserialize_with = "deserialize_unique_map")]
    releases: BTreeMap<String, ReleaseFile>,
}

/// Deserialized metadata for one release.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ReleaseFile {
    /// Serialized Luau bytecode version emitted by the release.
    bytecode: u8,
    /// Assets keyed by semantic platform name.
    #[serde(deserialize_with = "deserialize_unique_map")]
    assets: BTreeMap<String, AssetFile>,
}

/// URL and digest for one platform archive.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct AssetFile {
    /// Exact GitHub release download URL.
    url: String,
    /// Lowercase SHA-256 digest of the complete archive.
    sha256: String,
}

/// Serde visitor that preserves a JSON object while rejecting duplicate keys.
struct UniqueMapVisitor<Value> {
    /// Associates the visitor with the value type it asks Serde to construct.
    marker: PhantomData<Value>,
}

impl<'de, Value> Visitor<'de> for UniqueMapVisitor<Value>
where
    Value: Deserialize<'de>,
{
    type Value = BTreeMap<String, Value>;

    /// Describes the duplicate-free JSON object required by the registry schema.
    fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("a JSON object without duplicate keys")
    }

    /// Deserializes every entry while failing before a repeated key can replace data.
    fn visit_map<Access>(self, mut access: Access) -> Result<Self::Value, Access::Error>
    where
        Access: MapAccess<'de>,
    {
        let mut values = BTreeMap::new();
        while let Some((key, value)) = access.next_entry::<String, Value>()? {
            if values.contains_key(&key) {
                return Err(Access::Error::custom(format!(
                    "duplicate registry object key {key:?}"
                )));
            }
            values.insert(key, value);
        }
        Ok(values)
    }
}

/// Deserializes a registry object without Serde's usual last-value-wins behavior.
fn deserialize_unique_map<'de, DeserializerType, Value>(
    deserializer: DeserializerType,
) -> Result<BTreeMap<String, Value>, DeserializerType::Error>
where
    DeserializerType: Deserializer<'de>,
    Value: Deserialize<'de>,
{
    deserializer.deserialize_map(UniqueMapVisitor {
        marker: PhantomData,
    })
}

/// Stable output order and Rust target mapping for semantic platform names.
const ASSET_ORDER: [(&str, &str, &str); 4] = [
    (
        "windows-x86_64",
        "x86_64-pc-windows-msvc",
        "luau-windows.zip",
    ),
    (
        "linux-x86_64",
        "x86_64-unknown-linux-gnu",
        "luau-ubuntu.zip",
    ),
    ("macos-x86_64", "x86_64-apple-darwin", "luau-macos.zip"),
    ("macos-aarch64", "aarch64-apple-darwin", "luau-macos.zip"),
];

/// Abort compilation with a registry-specific actionable diagnostic.
fn fail(message: impl AsRef<str>) -> ! {
    panic!("registry.json validation failed: {}", message.as_ref());
}

/// Parse and validate a release key in the canonical `0.xxx` form.
fn version_number(version: &str) -> u32 {
    let Some(suffix) = version.strip_prefix("0.") else {
        fail(format!("release key {version:?} must use the 0.xxx format"));
    };
    if suffix.len() != 3 || !suffix.chars().all(|character| character.is_ascii_digit()) {
        fail(format!("release key {version:?} must use the 0.xxx format"));
    }
    suffix.parse::<u32>().unwrap_or_else(|_| {
        fail(format!(
            "release key {version:?} has a numeric suffix outside u32 range"
        ))
    })
}

/// Validate a digest's representation and reject a sentinel all-zero value.
fn validate_hash(version: &str, platform: &str, hash: &str) {
    if hash.len() != 64
        || !hash
            .bytes()
            .all(|character| character.is_ascii_digit() || (b'a'..=b'f').contains(&character))
    {
        fail(format!(
            "release {version}, asset {platform} has a SHA-256 that is not 64 lowercase hex characters"
        ));
    }
    if hash.bytes().all(|character| character == b'0') {
        fail(format!(
            "release {version}, asset {platform} has an all-zero SHA-256"
        ));
    }
}

/// Resolve a semantic platform to its Rust target and upstream archive name.
fn asset_spec(platform: &str) -> (&'static str, &'static str) {
    ASSET_ORDER
        .iter()
        .find(|(name, _, _)| *name == platform)
        .map(|(_, target, archive)| (*target, *archive))
        .unwrap_or_else(|| fail(format!("unknown asset platform {platform:?}")))
}

/// Validate every invariant required before generated code can be compiled.
fn validate_release(version: &str, release: &ReleaseFile) {
    let _ = version_number(version);
    if !(4..=11).contains(&release.bytecode) {
        fail(format!(
            "release {version} has bytecode {}; supported range is 4..=11",
            release.bytecode
        ));
    }
    if release.assets.len() != 3 {
        fail(format!(
            "release {version} must contain exactly Windows, Linux, and one macOS asset (found {})",
            release.assets.len()
        ));
    }
    for platform in release.assets.keys() {
        let _ = asset_spec(platform);
    }
    for required in ["windows-x86_64", "linux-x86_64"] {
        if !release.assets.contains_key(required) {
            fail(format!(
                "release {version} is missing required {required} asset"
            ));
        }
    }
    let mac_count = ["macos-x86_64", "macos-aarch64"]
        .iter()
        .filter(|platform| release.assets.contains_key(**platform))
        .count();
    if mac_count != 1 {
        fail(format!(
            "release {version} must contain exactly one of macos-x86_64 or macos-aarch64"
        ));
    }
    for (platform, asset) in &release.assets {
        let (_, archive) = asset_spec(platform);
        let expected_url =
            format!("https://github.com/luau-lang/luau/releases/download/{version}/{archive}");
        if asset.url != expected_url {
            fail(format!(
                "release {version}, asset {platform} URL must be exactly {expected_url:?} (got {:?})",
                asset.url
            ));
        }
        validate_hash(version, platform, &asset.sha256);
    }
}

/// Convert a release key into a valid and deterministic static identifier.
fn rust_identifier(version: &str) -> String {
    format!("ASSETS_{}", version.replace('.', "_"))
}

/// Render the library enum variant requested by the generated source contract.
fn bytecode_variant(number: u8) -> String {
    format!("BytecodeVersion::V{number}")
}

/// Render static platform arrays and a newest-first release slice.
fn generate(registry: &RegistryFile) -> String {
    let mut releases: Vec<(&String, &ReleaseFile)> = registry.releases.iter().collect();
    releases.sort_by_key(|(version, _)| std::cmp::Reverse(version_number(version)));

    let mut output = String::from(
        "// @generated by crates/mallow-luau-toolchain/build.rs; do not edit by hand.\n\n",
    );
    for (version, release) in &releases {
        let identifier = rust_identifier(version);
        writeln!(output, "static {identifier}: [PlatformAsset; 3] = [")
            .expect("writing generated source to a String is infallible");
        for (platform, _, _) in ASSET_ORDER
            .iter()
            .filter(|(name, _, _)| release.assets.contains_key(*name))
        {
            let asset = release.assets.get(*platform).expect("validated asset");
            let (target, archive) = asset_spec(platform);
            writeln!(
                output,
                "    PlatformAsset {{ target: {target:?}, archive_name: {archive:?}, url: {:?}, sha256: {:?} }},",
                asset.url, asset.sha256
            )
            .expect("writing generated source to a String is infallible");
        }
        output.push_str("];\n\n");
    }
    writeln!(output, "static RELEASES: [Release; {}] = [", releases.len())
        .expect("writing generated source to a String is infallible");
    for (version, release) in releases {
        writeln!(
            output,
            "    Release {{ version: {version:?}, bytecode: {}, assets: &{} }},",
            bytecode_variant(release.bytecode),
            rust_identifier(version)
        )
        .expect("writing generated source to a String is infallible");
    }
    output.push_str("];\n\n/// Returns releases newest-first from the validated generated registry.\npub(super) fn registry() -> &'static [Release] {\n    &RELEASES\n}\n");
    output
}

/// Deserialize, validate, and emit the compile-time registry.
fn main() {
    println!("cargo:rerun-if-changed=registry.json");
    println!("cargo:rerun-if-changed=build.rs");

    let manifest_dir = env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR is set");
    let registry_path = Path::new(&manifest_dir).join("registry.json");
    let bytes = fs::read(&registry_path).unwrap_or_else(|error| {
        panic!(
            "could not read {}: {error}; create the canonical registry JSON or run scripts/seed-registry.nu",
            registry_path.display()
        )
    });
    let registry: RegistryFile = serde_json::from_slice(&bytes)
        .unwrap_or_else(|error| panic!("could not parse {}: {error}", registry_path.display()));
    if registry.schema != SCHEMA {
        fail(format!(
            "unsupported schema {}; this crate expects schema {SCHEMA}",
            registry.schema
        ));
    }
    if registry.releases.is_empty() {
        fail("releases must contain at least one entry");
    }
    for (version, release) in &registry.releases {
        validate_release(version, release);
    }
    let out_dir = env::var_os("OUT_DIR").expect("OUT_DIR is set");
    fs::write(
        Path::new(&out_dir).join("registry_generated.rs"),
        generate(&registry),
    )
    .expect("write OUT_DIR/registry_generated.rs");
}
