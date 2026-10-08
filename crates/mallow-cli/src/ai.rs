//! LLM-suggested local names for decompiled source, requested through OpenRouter.

use std::time::Duration;

use anyhow::{Context, Result, bail};
use clap::ValueEnum;
use mallow_core::{DecompiledSource, LUAU_KEYWORDS, RenameReport};
use reqwest::blocking::Client;
use reqwest::header::CONTENT_TYPE;
use serde_json::{Value, json};

use crate::diagnostics;

/// OpenRouter's OpenAI-compatible chat completions endpoint.
const ENDPOINT: &str = "https://openrouter.ai/api/v1/chat/completions";

/// Environment variable holding the OpenRouter API key.
const API_KEY_VAR: &str = "OPENROUTER_API_KEY";

/// Model used when `--ai-rename` is given without a value.
pub const DEFAULT_MODEL: &str = "anthropic/claude-sonnet-5.5";

/// Diagnostic target label for AI renaming lines.
pub const LOG_TARGET: &str = "ai";

/// Upper bound for one completion, which can be slow on large sources.
const REQUEST_TIMEOUT: Duration = Duration::from_secs(300);

/// Builds the system prompt.
///
/// `rename_locals` enforces these rules again and skips or fixes suggestions that break
/// them; stating them here only makes those fallbacks rare.
fn system_prompt() -> String {
    format!(
        "\
You are assisting a Luau decompiler. Decompiled code has lost its local variable names, \
so they appear as placeholders such as p0 (parameters) and v12 (other locals). \
Infer a descriptive name for each placeholder from how it is used.

Reply with a single JSON object that maps placeholders to new names, for example \
{{\"v34\": \"player\", \"p0\": \"self\"}}. Rules:
- Only use keys from the given list of placeholders. Never rename globals, fields, or methods.
- Values must be valid Luau identifiers: ASCII letters, digits, and underscores, not \
starting with a digit or an underscore.
- Values must not be one of these keywords: {keywords}.
- Every value must be unique, and must not match any name already in the code, \
including globals such as print or game.
- Prefer the camelCase style usual in Luau.
- Leave out placeholders whose purpose you cannot infer instead of guessing.
- Reply with only the raw JSON object: no code fences, no explanation.",
        keywords = LUAU_KEYWORDS.join(", ")
    )
}

/// How much the model may reason before answering.
#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum Reasoning {
    /// Answer without reasoning.
    Off,
    /// Reason briefly.
    Low,
    /// Reason moderately.
    Medium,
    /// Reason at length.
    High,
}

impl Reasoning {
    /// Returns OpenRouter's `reasoning` request field. Reasoning text is excluded from
    /// the reply so the message content stays the bare JSON object.
    fn request(self) -> Value {
        let effort = match self {
            Self::Off => return json!({ "enabled": false }),
            Self::Low => "low",
            Self::Medium => "medium",
            Self::High => "high",
        };
        json!({ "effort": effort, "exclude": true })
    }
}

/// An OpenRouter model that suggests local names.
pub struct AiRenamer {
    api_key: String,
    model: String,
    reasoning: Reasoning,
}

impl AiRenamer {
    /// Reads the API key from the environment.
    pub fn from_env(model: &str, reasoning: Reasoning) -> Result<Self> {
        let api_key = std::env::var(API_KEY_VAR)
            .with_context(|| format!("--ai-rename needs an OpenRouter API key in {API_KEY_VAR}"))?;
        Ok(Self {
            api_key,
            model: model.to_owned(),
            reasoning,
        })
    }

    /// Asks the model for better local names and applies the valid suggestions.
    pub fn rename(&self, source: &mut DecompiledSource) -> Result<RenameReport> {
        let locals = source.local_names();
        if locals.is_empty() {
            return Ok(RenameReport::default());
        }
        let prompt = format!(
            "Placeholders: {}\n\n```lua\n{}```",
            locals.join(", "),
            source.print()
        );
        diagnostics::notice(
            LOG_TARGET,
            0,
            format_args!(
                "decompilation finished, waiting for {} renames...",
                self.model
            ),
        );
        let reply = self.complete(&prompt)?;
        let renames = parse_renames(&reply)?;
        Ok(source.rename_locals(renames))
    }

    /// Sends one chat completion request and returns the reply text.
    fn complete(&self, prompt: &str) -> Result<String> {
        let body = json!({
            "model": self.model,
            "messages": [
                { "role": "system", "content": system_prompt() },
                { "role": "user", "content": prompt },
            ],
            "response_format": { "type": "json_object" },
            "reasoning": self.reasoning.request(),
        });
        let response = Client::new()
            .post(ENDPOINT)
            .timeout(REQUEST_TIMEOUT)
            .bearer_auth(&self.api_key)
            .header(CONTENT_TYPE, "application/json")
            .header("X-Title", "mallow")
            .body(serde_json::to_vec(&body)?)
            .send()
            .context("OpenRouter request failed")?;

        let status = response.status();
        let text = response
            .text()
            .context("failed to read the OpenRouter response")?;
        let value: Value = serde_json::from_str(&text)
            .with_context(|| format!("OpenRouter returned {status} with a non-JSON body"))?;
        if !status.is_success() {
            let message = value["error"]["message"].as_str().unwrap_or(&text);
            bail!("OpenRouter returned {status}: {message}");
        }
        value["choices"][0]["message"]["content"]
            .as_str()
            .map(str::to_owned)
            .context("OpenRouter response has no message content")
    }

    /// Writes a summary of one rename to the diagnostics output, listing skipped suggestions when verbose.
    pub fn report(&self, report: &RenameReport, verbose: bool) {
        diagnostics::notice(
            LOG_TARGET,
            0,
            format_args!(
                "{} renamed {} locals ({} suggestions skipped)",
                self.model,
                report.applied.len(),
                report.skipped.len()
            ),
        );
        if verbose {
            for skipped in &report.skipped {
                diagnostics::notice(
                    LOG_TARGET,
                    1,
                    format_args!(
                        "skipped {} -> {}: {}",
                        skipped.from, skipped.to, skipped.reason
                    ),
                );
            }
        }
    }
}

/// Reads the `{ "old": "new" }` object that makes up the whole reply.
fn parse_renames(reply: &str) -> Result<Vec<(String, String)>> {
    let object: serde_json::Map<String, Value> =
        serde_json::from_str(reply.trim()).context("the model reply is not a bare JSON object")?;
    Ok(object
        .into_iter()
        .filter_map(|(from, to)| Some((from, to.as_str()?.to_owned())))
        .collect())
}
