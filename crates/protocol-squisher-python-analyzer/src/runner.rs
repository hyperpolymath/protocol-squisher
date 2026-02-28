// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Python script execution for Pydantic introspection

use crate::types::IntrospectionResult;
use crate::AnalyzerError;
use std::process::{Command, Stdio};

/// The embedded Python introspection script
pub const INTROSPECTION_SCRIPT: &str = include_str!("../scripts/introspect_pydantic.py");

/// Configuration for the Python runner
#[derive(Debug, Clone)]
pub struct PythonRunnerConfig {
    /// Python interpreter to use
    pub python_path: String,
    /// Additional Python path entries
    pub pythonpath: Vec<String>,
    /// Working directory for the Python process
    pub working_dir: Option<String>,
    /// Environment variables to set
    pub env: Vec<(String, String)>,
}

impl Default for PythonRunnerConfig {
    fn default() -> Self {
        Self {
            python_path: "python3".to_string(),
            pythonpath: vec![],
            working_dir: None,
            env: vec![],
        }
    }
}

/// Run the Python introspection script
pub fn run_introspection(
    module_path: &str,
    model_names: &[String],
    config: &PythonRunnerConfig,
) -> Result<IntrospectionResult, AnalyzerError> {
    // Build command
    let mut cmd = Command::new(&config.python_path);
    cmd.arg("-c").arg(INTROSPECTION_SCRIPT).arg(module_path);

    // Add model names if specified
    for name in model_names {
        cmd.arg(name);
    }

    // Set up pipes
    cmd.stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    // Set working directory
    if let Some(ref dir) = config.working_dir {
        cmd.current_dir(dir);
    }

    // Build PYTHONPATH
    if !config.pythonpath.is_empty() {
        let existing = std::env::var("PYTHONPATH").unwrap_or_default();
        let mut paths: Vec<&str> = config.pythonpath.iter().map(|s| s.as_str()).collect();
        if !existing.is_empty() {
            paths.push(&existing);
        }
        cmd.env("PYTHONPATH", paths.join(":"));
    }

    // Set additional environment variables
    for (key, value) in &config.env {
        cmd.env(key, value);
    }

    // Run the command
    let output = cmd
        .output()
        .map_err(|e| AnalyzerError::PythonError(format!("Failed to run Python: {e}")))?;

    // Check for execution errors
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let details = if !stderr.trim().is_empty() {
            stderr.to_string()
        } else if !stdout.trim().is_empty() {
            stdout.to_string()
        } else {
            format!("exit status: {}", output.status)
        };
        return Err(AnalyzerError::PythonError(format!(
            "Python script failed: {}",
            enrich_failure_details(details)
        )));
    }

    // Parse the JSON output
    let stdout = String::from_utf8_lossy(&output.stdout);
    serde_json::from_str(&stdout).map_err(|e| {
        AnalyzerError::PythonError(format!(
            "Failed to parse introspection output: {e}\nOutput: {stdout}"
        ))
    })
}

/// Run the introspection script with a custom script (for testing)
pub fn run_introspection_with_script(
    script: &str,
    module_path: &str,
    config: &PythonRunnerConfig,
) -> Result<IntrospectionResult, AnalyzerError> {
    let mut cmd = Command::new(&config.python_path);
    cmd.arg("-c").arg(script).arg(module_path);

    cmd.stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    if let Some(ref dir) = config.working_dir {
        cmd.current_dir(dir);
    }

    let output = cmd
        .output()
        .map_err(|e| AnalyzerError::PythonError(format!("Failed to run Python: {e}")))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let details = if !stderr.trim().is_empty() {
            stderr.to_string()
        } else if !stdout.trim().is_empty() {
            stdout.to_string()
        } else {
            format!("exit status: {}", output.status)
        };
        return Err(AnalyzerError::PythonError(format!(
            "Python script failed: {}",
            enrich_failure_details(details)
        )));
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    serde_json::from_str(&stdout).map_err(|e| {
        AnalyzerError::PythonError(format!("Failed to parse introspection output: {e}"))
    })
}

/// Check if Python and Pydantic are available
pub fn check_python_available(config: &PythonRunnerConfig) -> Result<bool, AnalyzerError> {
    let check_script = r#"
import sys
import json
try:
    import pydantic
    print(json.dumps({"available": True, "version": pydantic.VERSION}))
except ImportError:
    print(json.dumps({"available": False, "error": "Pydantic not installed"}))
"#;

    let output = Command::new(&config.python_path)
        .arg("-c")
        .arg(check_script)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .map_err(|e| AnalyzerError::PythonError(format!("Failed to run Python: {e}")))?;

    if !output.status.success() {
        return Ok(false);
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let result: serde_json::Value = serde_json::from_str(&stdout).map_err(|_| {
        AnalyzerError::PythonError("Failed to parse Python check output".to_string())
    })?;

    Ok(result
        .get("available")
        .and_then(|v| v.as_bool())
        .unwrap_or(false))
}

fn enrich_failure_details(details: String) -> String {
    if details.contains("Pydantic not installed") {
        format!(
            "{details}\nInstall with: `python3 -m pip install pydantic` (or activate the intended virtual environment first)"
        )
    } else {
        details
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_script_embedded() {
        // Verify the embedded introspection script has expected anchors.
        assert!(INTROSPECTION_SCRIPT.contains("introspect_module"));
        assert!(INTROSPECTION_SCRIPT.contains("pydantic"));
    }

    #[test]
    fn test_default_config() {
        let config = PythonRunnerConfig::default();
        assert_eq!(config.python_path, "python3");
        assert!(config.pythonpath.is_empty());
    }

    // Integration tests would require Python to be available
    // They are marked with #[ignore] and run with --ignored
    #[test]
    #[ignore]
    fn test_check_python() {
        let config = PythonRunnerConfig::default();
        let result = check_python_available(&config);
        assert!(result.is_ok());
    }
}
