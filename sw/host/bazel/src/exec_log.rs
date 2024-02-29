// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// use anyhow::{bail, Result};
use serde::de::Error;
use serde::ser::SerializeSeq;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::HashMap;

use spawn_proto::protos::{Digest as BazelDigest, File as BazelFile, SpawnExec};

#[derive(Default)]
struct IndexedSet<T: Default> {
    values: Vec<T>,
    map: HashMap<T, usize>,
}

impl<T> IndexedSet<T>
where
    T: Default + Clone + Eq + std::hash::Hash,
{
    pub fn get_or_insert(&mut self, val: &T) -> usize {
        let new_index = self.values.len();
        let index = self.map.entry(val.clone()).or_insert(new_index);
        if *index == new_index {
            self.values.push(val.clone());
        }
        *index
    }
}

impl<T: Default> std::fmt::Debug for IndexedSet<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_struct("IndexedSet")
            .field("values (count)", &self.values.len())
            .finish()
    }
}

impl<T> Serialize for IndexedSet<T>
where
    T: Default + Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.values.len()))?;
        for e in &self.values {
            seq.serialize_element(e)?;
        }
        seq.end()
    }
}

impl<'de, T> Deserialize<'de> for IndexedSet<T>
where
    T: Default + Deserialize<'de>,
{
    fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Err(D::Error::custom("unimplemented".to_string()))
    }
}

#[derive(Default, Serialize, Deserialize)]
pub struct ExecLog {
    // List of all strings.
    strings: IndexedSet<String>,
    // List of all digests.
    digests: IndexedSet<Digest>,
    // List of all files.
    files: IndexedSet<File>,
    // List of entries in the log.
    entries: Vec<Entry>,
}

impl ExecLog {
    pub fn new() -> ExecLog {
        ExecLog::default()
    }

    fn add_bazel_digest(&mut self, digest: &BazelDigest) -> usize {
        self.digests.get_or_insert(&Digest {
            hash: self.strings.get_or_insert(&digest.hash),
            size_bytes: digest.size_bytes as u64,
            hash_fn: self.strings.get_or_insert(&digest.hash_function_name),
        })
    }

    fn add_bazel_file(&mut self, file: &BazelFile) -> usize {
        let digest = file.digest.as_ref().map(|d| self.add_bazel_digest(d));
        self.files.get_or_insert(&File {
            path: self.strings.get_or_insert(&file.path),
            symlink: self.strings.get_or_insert(&file.symlink_target_path),
            digest,
            is_tool: file.is_tool,
        })
    }

    pub fn add_bazel_entry(&mut self, entry: &SpawnExec) {
        let cmd_args = entry
            .command_args
            .iter()
            .map(|s| self.strings.get_or_insert(s))
            .collect::<Vec<_>>();
        let env_vars = entry
            .environment_variables
            .iter()
            .map(|ev| EnvVar {
                name: self.strings.get_or_insert(&ev.name),
                value: self.strings.get_or_insert(&ev.value),
            })
            .collect::<Vec<_>>();
        let inputs = entry
            .inputs
            .iter()
            .map(|e| self.add_bazel_file(e))
            .collect::<Vec<_>>();
        let listed_outputs = entry
            .listed_outputs
            .iter()
            .map(|s| self.strings.get_or_insert(s))
            .collect::<Vec<_>>();
        let actual_outputs = entry
            .actual_outputs
            .iter()
            .map(|e| self.add_bazel_file(e))
            .collect::<Vec<_>>();

        let entry = Entry {
            cmd_args,
            env_vars,
            inputs,
            listed_outputs,
            remotable: entry.remotable,
            cacheable: entry.cacheable,
            timeout_millis: entry.timeout_millis,
            mnemonic: self.strings.get_or_insert(&entry.mnemonic),
            actual_outputs,
            runner: self.strings.get_or_insert(&entry.runner),
            cache_hit: entry.cache_hit,
            status: self.strings.get_or_insert(&entry.status),
            exit_code: entry.exit_code,
            remote_cacheable: entry.remote_cacheable,
            target_label: self.strings.get_or_insert(&entry.target_label),
            digest: entry.digest.as_ref().map(|d| self.add_bazel_digest(d)),
        };
        self.entries.push(entry);
    }
}

impl std::fmt::Debug for ExecLog {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_struct("ExecLog")
            .field("strings", &self.strings)
            .field("digests", &self.digests)
            .field("files", &self.files)
            .field("entries (count)", &self.entries.len())
            .finish()
    }
}

#[derive(Default, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct Digest {
    /// The content hash as a lowercase hex string including any leading zeroes.
    hash: usize,
    /// The original content size in bytes.
    size_bytes: u64,
    /// The name of the digest function used to compute the hash.
    hash_fn: usize,
}

#[derive(Default, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct File {
    path: usize,
    symlink: usize,
    digest: Option<usize>,
    is_tool: bool,
}

#[derive(Default, Debug, Serialize, Deserialize)]
pub struct EnvVar {
    // Name (index into `ExecLog.strings`).
    name: usize,
    // Value (index into `ExecLog.strings`).
    value: usize,
}

#[derive(Default, Debug, Serialize, Deserialize)]
pub struct Entry {
    // List if command arguments (index into `ExecLog.strings`).
    cmd_args: Vec<usize>,
    // The command environment.
    env_vars: Vec<EnvVar>,
    // /// The command execution platform.
    // pub platform: ::core::option::Option<Platform>,
    // The inputs at the time of the execution (index into `ExecLog.files`).
    inputs: Vec<usize>,
    // All the listed outputs paths. The paths are relative to the execution root.
    // Actual outputs are a subset of the listed outputs. These paths are sorted.
    listed_outputs: Vec<usize>,
    // Whether the spawn was allowed to run remotely.
    remotable: bool,
    // Whether the spawn was allowed to be cached.
    cacheable: bool,
    // The spawn timeout.
    timeout_millis: i64,
    // The mnemonic of the action this spawn belongs to.
    mnemonic: usize,
    // The outputs generated by the execution.
    // In order for one of the listed_outputs to appear here, it must have been
    // produced and have the expected type (file, directory or symlink).
    actual_outputs: Vec<usize>,
    // If the spawn did not hit a disk or remote cache, this will be the name of
    // the runner, e.g. "remote", "linux-sandbox" or "worker".
    //
    // If the spawn hit a disk or remote cache, this will be "disk cache hit" or
    // "remote cache hit", respectively. This includes the case where a remote
    // cache was hit while executing the spawn remotely.
    //
    // Note that spawns whose owning action hits the persistent action cache
    // are never reported at all.
    //
    // This won't always match the spawn strategy. For the dynamic strategy, it
    // will be the runner for the first branch to complete. For the remote
    // strategy, it might be a local runner in case of a fallback.
    runner: usize,
    // Whether the spawn hit a disk or remote cache.
    cache_hit: bool,
    // A text status describing an execution error. Empty in case of success.
    status: usize,
    // This field contains the contents of SpawnResult.exitCode.
    // Its semantics varies greatly depending on the status field.
    // Dependable: if status is empty, exit_code is guaranteed to be zero.
    exit_code: i32,
    /// Whether the spawn was allowed to be cached remotely.
    remote_cacheable: bool,
    /// The canonical label of the target this spawn belongs to.
    target_label: usize,
    // The action cache digest.
    // Only available when remote execution, remote cache or disk cache was
    // enabled for this spawn.
    digest: Option<usize>,
    // /// Timing, size and memory statistics.
    // pub metrics: ::core::option::Option<SpawnMetrics>,
}
