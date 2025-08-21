// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::sync::LazyLock;
use std::task::{Context, Poll};
use std::time::Duration;

use tokio::runtime::Runtime;

static RUNTIME: LazyLock<Runtime> = LazyLock::new(|| Runtime::new().unwrap());

pub fn runtime() -> &'static Runtime {
    &RUNTIME
}

/// Block on a future to complete.
///
/// As opentitanlib is currently messy with its use MIO, to aid migration we allow this to be called within async context too.
pub fn block_on<F: Future>(future: F) -> F::Output {
    tokio::task::block_in_place(|| runtime().block_on(future))
}

/// Ask the runtime to poll `timeout` later.
///
/// This is a helper function for things that do not yet support notification when they're ready and require
/// continuous polling with timeouts.
pub fn poll_later<T>(cx: &mut Context<'_>, timeout: Duration) -> Poll<T> {
    let waker = cx.waker().clone();
    runtime().spawn(async move {
        tokio::time::sleep(timeout).await;
        waker.wake();
    });
    Poll::Pending
}
