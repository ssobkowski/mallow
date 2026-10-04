#!/usr/bin/env python3

from __future__ import annotations

import hashlib
import io
import json
import os
import re
import stat
import struct
import subprocess
import sys
import tempfile
import urllib.request
import zipfile
from pathlib import Path

REPO = "luau-lang/luau"
REGISTRY = (
    Path(__file__).resolve().parent.parent
    / "crates/mallow-luau-toolchain/registry.json"
)
ARCHIVES = {
    "windows-x86_64": "luau-windows.zip",
    "linux-x86_64": "luau-ubuntu.zip",
    "macos": "luau-macos.zip",
}

# Luau doesn't ship x86-64 releases for macos anymore but whatever
MACHO_CPU = {0x01000007: "macos-x86_64", 0x0100000C: "macos-aarch64"}


def fetch(url: str, accept: str | None = None) -> bytes:
    request = urllib.request.Request(url)
    if accept:
        request.add_header("Accept", accept)
    if token := os.environ.get("GITHUB_TOKEN"):
        request.add_header("Authorization", f"Bearer {token}")
    with urllib.request.urlopen(request) as response:
        return response.read()


def minor(version: str) -> int:
    return int(version.removeprefix("0."))


def upstream_releases() -> list[str]:
    versions = []
    page = 1
    while True:
        url = f"https://api.github.com/repos/{REPO}/releases?per_page=100&page={page}"
        batch = json.loads(fetch(url, "application/vnd.github+json"))
        if not batch:
            return versions
        versions += [
            release["tag_name"]
            for release in batch
            if not release["draft"]
            and not release["prerelease"]
            and re.fullmatch(r"0\.\d+", release["tag_name"])
        ]
        page += 1


def bytecode_version(archive: bytes) -> int:
    with tempfile.TemporaryDirectory() as directory:
        compiler = Path(directory) / "luau-compile"
        compiler.write_bytes(zipfile.ZipFile(io.BytesIO(archive)).read("luau-compile"))
        compiler.chmod(compiler.stat().st_mode | stat.S_IXUSR)
        source = Path(directory) / "probe.luau"
        source.write_text("local x = 1\nprint(x)\n")
        output = subprocess.run(
            [compiler, "--binary", source], check=True, capture_output=True
        ).stdout
    return output[0]


def macos_platform(version: str, archive: bytes) -> str:
    binary = zipfile.ZipFile(io.BytesIO(archive)).read("luau-compile")
    magic, cpu = struct.unpack("<II", binary[:8])
    if magic != 0xFEEDFACF or cpu not in MACHO_CPU:
        sys.exit(
            f"{version}: unrecognized macOS binary (magic {magic:#x}, cpu {cpu:#x})"
        )
    return MACHO_CPU[cpu]


def describe(version: str) -> dict:
    assets = {}
    bytecode = None
    for platform, name in ARCHIVES.items():
        url = f"https://github.com/{REPO}/releases/download/{version}/{name}"
        print(f"  {url}", file=sys.stderr)
        archive = fetch(url)
        if platform == "macos":
            platform = macos_platform(version, archive)
        elif platform == "linux-x86_64":
            bytecode = bytecode_version(archive)
        assets[platform] = {"url": url, "sha256": hashlib.sha256(archive).hexdigest()}
    return {"bytecode": bytecode, "assets": assets}


def main() -> None:
    registry = json.loads(REGISTRY.read_text())
    newest = max(map(minor, registry["releases"]))
    pending = sorted((v for v in upstream_releases() if minor(v) > newest), key=minor)
    if not pending:
        print(f"registry is up to date (0.{newest})", file=sys.stderr)
        return

    releases = registry["releases"]
    for version in pending:
        print(f"adding {version}", file=sys.stderr)
        releases[version] = describe(version)
        print(f"  bytecode {releases[version]['bytecode']}", file=sys.stderr)

    registry["releases"] = dict(
        sorted(releases.items(), key=lambda item: -minor(item[0]))
    )
    REGISTRY.write_text(json.dumps(registry, indent=2) + "\n")
    print(", ".join(pending))


if __name__ == "__main__":
    main()
