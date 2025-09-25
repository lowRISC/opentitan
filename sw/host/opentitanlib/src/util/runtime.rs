// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Arc, LazyLock, Mutex};
use std::task::{Context, Poll, Wake, Waker};
use std::time::Duration;

use anyhow::Result;
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

struct MultiWakerInner {
    // A counter that is incremented every time wake happens.
    generation: AtomicU32,
    wakers: Mutex<Vec<Waker>>,
}

impl Wake for MultiWakerInner {
    fn wake(self: Arc<Self>) {
        self.wake_by_ref();
    }

    fn wake_by_ref(self: &Arc<Self>) {
        let mut guard = self.wakers.lock().unwrap();
        let wakers = std::mem::take(&mut *guard);
        self.generation.fetch_add(1, Ordering::Relaxed);
        drop(guard);

        for waker in wakers {
            waker.wake();
        }
    }
}

/// A utility type ensures that multiple pollers can all be waken up.
///
/// With `tokio`'s design, `poll_*` functions will only wake up the waker associated with the last poller.
/// This works well with tokio's types, however due to OT-lib design issues, we might have multiple pollers
/// (e.g. `Uart`'s API takes `&self` instead of `&mut self`). This utility ensures that even if multiple pollers
/// are present, no wake messages will be lost.
pub struct MultiWaker {
    inner: Arc<MultiWakerInner>,
}

/// A intent to register a waker to `MultiWaker`.
///
/// When registration eventually happens, it is treated as if the registration happens at the point in time when
/// the instance of this type is created.
///
/// Dropping this type without registration is a cheap no-op.
pub struct MultiWakerRegistration<'a> {
    generation: u32,
    waker: &'a MultiWakerInner,
}

impl<'a> MultiWakerRegistration<'a> {
    /// Complete the registration of waker.
    pub fn register(self, waker: &Waker) {
        // When we received pending, we need to register the waker.
        let mut guard = self.waker.wakers.lock().unwrap();
        let generation = self.waker.generation.load(Ordering::Relaxed);
        if generation == self.generation {
            if guard.iter().all(|w| !w.will_wake(waker)) {
                guard.push(waker.clone());
            }
        } else {
            // Conceptually, we registered `waker` at the point of creation of `self`.
            // If generation number changes, it means our waker has been `wake()`-ed since creation,
            // so we need to invoke the waker immediately.
            drop(guard);
            waker.wake_by_ref();
        }
    }
}

impl MultiWaker {
    /// Create a new `MultiWaker`.
    pub fn new() -> Self {
        Self {
            inner: Arc::new(MultiWakerInner {
                generation: AtomicU32::new(0),
                wakers: Mutex::new(Vec::new()),
            }),
        }
    }

    /// Obtain a waker that can be used to wake up all registered wakers.
    pub fn waker(&self) -> Waker {
        self.inner.clone().into()
    }

    /// Signal the intent to register a waker.
    ///
    /// When registration eventually happens, it is treated as if the registration happens at this point in time.
    /// This is a cheap operation compared to the actual registration of the waker.
    pub fn register(&self) -> MultiWakerRegistration<'_> {
        MultiWakerRegistration {
            generation: self.inner.generation.load(Ordering::Relaxed),
            waker: &self.inner,
        }
    }

    /// Call a polling function with the guarantee of not losing `Waker`.
    ///
    /// For the guarantee to be upheld the same `MultiWaker` instance should be used for every poll call.
    pub fn poll_with<T, F: FnOnce(&mut Context<'_>) -> Poll<T>>(
        &self,
        cx: &mut Context<'_>,
        f: F,
    ) -> Poll<T> {
        let waker = self.waker();
        let register = self.register();
        let mut new_cx = Context::from_waker(&waker);
        match f(&mut new_cx) {
            Poll::Ready(v) => Poll::Ready(v),
            Poll::Pending => {
                register.register(cx.waker());
                Poll::Pending
            }
        }
    }
}

impl Default for MultiWaker {
    fn default() -> Self {
        Self::new()
    }
}

/// Listen for shutdown signals.
pub async fn shutdown_signal() {
    let ctrl_c = async {
        tokio::signal::ctrl_c()
            .await
            .expect("failed to install Ctrl+C handler");
    };

    let terminate = async {
        tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate())
            .expect("failed to install signal handler")
            .recv()
            .await;
    };

    tokio::select! {
        biased;
        _ = ctrl_c => {},
        _ = terminate => {},
    }
}

/// Run a future with graceful shutdown.
pub async fn with_graceful_shutdown(fut: impl Future<Output = Result<()>>) -> Result<()> {
    tokio::select! {
        v = fut => v,
        _ = shutdown_signal() => Ok(()),
    }
}
