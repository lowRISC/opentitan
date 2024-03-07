// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde::de::Error;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};

use spawn_proto::protos::{Digest as BazelDigest, File as BazelFile, Platform as BazelPlatform, SpawnExec};

pub trait ViewType<'outer, Outer, T> {
    fn view_from(outer: &'outer Outer, val: &'outer T) -> Self;
}

#[derive(Default)]
struct IndexedSet<T: Default> {
    values: Vec<T>,
    map: HashMap<T, usize>,
}

pub struct IndexedSetIterator<'set, T: Default> {
    iter: <&'set Vec<T> as IntoIterator>::IntoIter,
}

impl<'set, T: Default> Iterator for IndexedSetIterator<'set, T> {
    type Item = &'set T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

pub struct IndexedSetIteratorWith<'outer, Outer, T: Default, ViewT>
where ViewT: ViewType<'outer, Outer, T>
{
    outer: &'outer Outer,
    iter: <&'outer Vec<T> as IntoIterator>::IntoIter,
    _viewt: std::marker::PhantomData<ViewT>,
}

impl<'outer, Outer, T: Default, ViewT> Iterator for IndexedSetIteratorWith<'outer, Outer, T, ViewT>
where ViewT: ViewType<'outer, Outer, T> {
    type Item = ViewT;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|x| ViewT::view_from(self.outer, x))
    }
}

impl<T> IndexedSet<T>
where
    T: Default + Clone + Eq + std::hash::Hash,
{
    pub fn get_at(&self, idx: usize) -> &T {
        &self.values[idx]
    }

    pub fn get_or_insert(&mut self, val: &T) -> usize {
        let new_index = self.values.len();
        let index = self.map.entry(val.clone()).or_insert(new_index);
        if *index == new_index {
            self.values.push(val.clone());
        }
        *index
    }

    pub fn iter(&self) -> IndexedSetIterator<T> {
        IndexedSetIterator {
            iter: (&self.values).into_iter(),
        }
    }

    pub fn iter_with<'outer, Outer, ViewT>(&'outer self, outer: &'outer Outer) -> IndexedSetIteratorWith<'outer, Outer, T, ViewT>
    where ViewT: ViewType<'outer, Outer, T> {
        IndexedSetIteratorWith {
            outer: outer,
            iter: (&self.values).into_iter(),
            _viewt: std::marker::PhantomData,
        }
    }
}

impl<T: Default> Debug for IndexedSet<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_struct("IndexedSet")
            .field("values (count)", &self.values.len())
            .finish()
    }
}

// For an IndexedSet, we only serialize the values.
impl<T> Serialize for IndexedSet<T>
where
    T: Default + Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.values.serialize(serializer)
    }
}

// For an IndexedSet, deserializes the value and reconstruct the map.
impl<'de, T> Deserialize<'de> for IndexedSet<T>
where
    T: Default + Eq + std::hash::Hash + Clone + Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let values = Vec::<T>::deserialize(deserializer)?;
        let mut map = HashMap::new();
        for (idx, val) in values.iter().enumerate() {
            if map.insert(val.clone(), idx).is_some() {
                return Err(D::Error::custom("indexed set contains duplicate entry".to_string()))
            }
        }
        Ok(IndexedSet {
            values,
            map
        })
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
    // List of all files.
    properties: IndexedSet<Property>,
    // List of entries in the log.
    entries: Vec<Entry>,
}

impl ExecLog {
    pub fn new() -> ExecLog {
        ExecLog::default()
    }

    pub fn iter_strings(&self) -> IndexedSetIterator<String> {
        self.strings.iter()
    }

    pub fn iter_files(&self) -> IndexedSetIteratorWith<Self, File, FileView> {
        self.files.iter_with(self)
    }

    fn add_property(&mut self, name: &String, value: &String) -> usize {
        let prop = Property {
            name: self.strings.get_or_insert(name),
            value: self.strings.get_or_insert(value),
        };
        self.properties.get_or_insert(&prop)
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

    fn add_bazel_platform(&mut self, platform: &BazelPlatform) -> Vec<usize> {
        platform.properties.iter().map(|p| self.add_property(&p.name, &p.value)).collect()
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
            .map(|ev| self.add_property(&ev.name, &ev.value))
            .collect::<Vec<_>>();
        let platform = entry.platform.as_ref().map(|p| self.add_bazel_platform(p)).unwrap_or_else(|| Vec::new());
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
            platform,
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
            .field("properties", &self.properties)
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

pub struct DigestView<'log> {
    exec_log: &'log ExecLog,
    digest: &'log Digest,
}

impl<'log> ViewType<'log, ExecLog, Digest> for DigestView<'log> {
    fn view_from(exec_log: &'log ExecLog, digest: &'log Digest) -> Self {
        DigestView {
            exec_log,
            digest
        }
    }
}

impl<'log> Debug for DigestView<'log> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_struct("File")
            .field("hash", &self.exec_log.strings.get_at(self.digest.hash))
            .field("size_bytes", &self.digest.size_bytes)
            .field("hash_fn", &self.exec_log.strings.get_at(self.digest.hash_fn))
            .finish()
    }
}

#[derive(Default, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct File {
    path: usize,
    symlink: usize,
    digest: Option<usize>,
    is_tool: bool,
}

pub struct FileView<'log> {
    exec_log: &'log ExecLog,
    file: &'log File,
}

impl FileView<'_> {
    pub fn path(&self) -> &str {
        &self.exec_log.strings.get_at(self.file.path)
    }

    pub fn digest(&self) -> Option<DigestView> {
        self.file.digest.map(|d_idx| {
            DigestView::view_from(self.exec_log, self.exec_log.digests.get_at(d_idx))
        })
    }

    pub fn symlink(&self) -> &str {
        &self.exec_log.strings.get_at(self.file.symlink)
    }

    pub fn is_tool(&self) -> bool {
        self.file.is_tool
    }
}

impl<'log> ViewType<'log, ExecLog, File> for FileView<'log> {
    fn view_from(exec_log: &'log ExecLog, file: &'log File) -> Self {
        FileView {
            exec_log,
            file
        }
    }
}

impl<'log> Debug for FileView<'log> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_struct("Digest")
            .field("path", &self.path())
            .field("symlink", &self.symlink())
            .field("digest", &self.digest())
            .field("is_tool", &self.is_tool())
            .finish()
    }
}

#[derive(Default, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct Property {
    // Name (index into `ExecLog.strings`).
    name: usize,
    // Value (index into `ExecLog.strings`).
    value: usize,
}

#[derive(Default, Debug, Serialize, Deserialize)]
pub struct Entry {
    // List if command arguments (index into `ExecLog.strings`).
    cmd_args: Vec<usize>,
    // The command environment variables (index into `ExecLog.properties`).
    env_vars: Vec<usize>,
    // The command execution platform (index into `ExecLog.properties`).
    platform: Vec<usize>,
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
