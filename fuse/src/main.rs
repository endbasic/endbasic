// EndBASIC
// Copyright 2026 Julio Merino
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

//! Command-line interface for the EndBASIC service FUSE filesystem.

use anyhow::Result;
use endbasic_client::PROD_API_ADDRESS;
use getoptsargs::prelude::*;

#[cfg(target_os = "linux")]
mod fs;

/// Errors caused by the user when invoking this binary.
#[derive(Debug, thiserror::Error)]
#[error("{message}")]
struct UsageError {
    message: String,
}

impl UsageError {
    /// Creates a new usage error with `message`.
    fn new<T: Into<String>>(message: T) -> Self {
        Self { message: message.into() }
    }
}

fn app_build(builder: Builder) -> Builder {
    builder
        .copyright("Copyright 2026 Julio Merino")
        .license(License::AGPL3OrLater)
        .homepage("https://www.endbasic.dev/")
        .bugs("https://github.com/endbasic/endbasic/issues")
        .optopt("", "password", "password to authenticate with", "PASSWORD")
        .optopt("", "service-url", "base URL of the cloud service", "URL")
        .optopt("", "user", "user name to authenticate with", "USERNAME")
        .trailarg("mountpoint", 1, 1, "directory on which to mount the filesystem")
}

fn app_main(matches: Matches) -> Result<i32> {
    let mountpoint = match matches.arg_trail() {
        [mountpoint] => mountpoint,
        _ => return Err(UsageError::new("Missing mountpoint argument").into()),
    };

    let username =
        matches.opt_str("user").ok_or_else(|| UsageError::new("Missing required --user option"))?;
    let password = matches
        .opt_str("password")
        .ok_or_else(|| UsageError::new("Missing required --password option"))?;
    let service_url = matches.opt_str("service-url").unwrap_or_else(|| PROD_API_ADDRESS.to_owned());

    #[cfg(target_os = "linux")]
    {
        fs::mount(service_url, username, password, mountpoint)?;
        Ok(0)
    }

    #[cfg(not(target_os = "linux"))]
    {
        let _ = (service_url, username, password, mountpoint);
        Err(UsageError::new("This binary is only supported on Linux").into())
    }
}

app!("EndBASIC FUSE", app_build, app_main);
