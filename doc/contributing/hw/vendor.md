---
title: Work with hardware code in external repositories
---

OpenTitan is not a closed ecosystem: we incorporate code from third parties, and we split out pieces of our code to reach a wider audience.
In both cases, we need to import and use code from external repositories in our OpenTitan code base.
Read on for step-by-step instructions for common tasks, and for background information on the topic.

## Summary

Code in subdirectories of `hw/vendor` is imported (copied in) from external repositories (which may be provided by lowRISC or other sources).
The external repository is called "upstream".
Any development on imported in `hw/vendor` code should happen upstream when possible.
Files ending with `.vendor.hjson` indicate where the upstream repository is located.

In particular, this means:

- If you find a bug in imported code or want to enhance it, report it upstream.
- Follow the rules and style guides of the upstream project.
   They might differ from our own rules.
- Use the upstream mechanisms to do code changes. In many cases, upstream uses GitHub just like we do with Pull Requests.
- Work with upstream reviewers to get your changes merged into their code base.
- Once the change is part of the upstream repository, the `util/vendor` tool can be used to copy the upstream code back into our OpenTitan repository.

Read on for the longer version of these guidelines.

Pushing changes upstream first isn't always possible or desirable: upstream might not accept changes, or be slow to respond.
In some cases, code changes are needed which are irrelevant for upstream and need to be maintained by us.
Our vendoring infrastructure is able to handle such cases, read on for more information on how to do it.

## Background

OpenTitan is developed in a "monorepo", a single repository containing all its source code.
This approach is beneficial for many reasons, ranging from an easier workflow to better reproducibility of the results, and that's why large companies like [Google](https://ai.google/research/pubs/pub45424) and Facebook are using monorepos.
Monorepos are even more compelling for hardware development, which cannot make use of a standardized language-specific package manager like npm or pip.

At the same time, open source is all about sharing and a free flow of code between projects.
We want to take in code from others, but also to give back and grow a wider ecosystem around our output.
To be able to do that, code repositories should be sufficiently modular and self-contained.
For example, if a CPU core is buried deep in a repository containing a full SoC design, people will have a hard time using this CPU core for their designs and contributing to it.

Our approach to this challenge: develop reusable parts of our code base in an external repository, and copy the source code back into our monorepo in an automated way.
The process of copying in external code is commonly called "vendoring".

Vendoring code is a good thing.
We continue to maintain a single code base which is easy to fork, tag and generally work with, as all the normal Git tooling works.
By explicitly importing code we also ensure that no unreviewed code sneaks into our code base, and a "always buildable" configuration is maintained.

But what happens if the imported code needs to be modified?
Ideally, all code changes are submitted upstream, integrated into the upstream code base, and then re-imported into our code base.
This development methodology is called "upstream first".
History has shown repeatedly that an upstream first policy can help significantly with the long-term maintenance of code.

However, strictly following an upstream first policy isn't great either.
Some changes might not be useful for the upstream community, others might be not acceptable upstream or only applied after a long delay.
In these situations it must be possible to modify the code downstream, i.e. in our repository, as well.
Our setup includes multiple options to achieve this goal.
In many cases, applying patches on top of the imported code is the most sustainable option.

To ease the pain points of vendoring code we have developed tooling and continue to do so.
Please open an issue ticket if you see areas where the tooling could be improved.

## Basic concepts

This section gives a quick overview how we include code from other repositories into our repository.

All imported ("vendored") hardware code is by convention put into the `hw/vendor` directory.
(We have more conventions for file and directory names which are discussed below when the import of new code is described.)
To interact with code in this directory a tool called `util/vendor.py` is used.
A "vendor description file" controls the vendoring process and serves as input to the `util/vendor` tool.

In the simple, yet typical, case, the vendor description file is only a couple of lines of human-readable JSON:

```command
$ cat hw/vendor/lowrisc_ibex.vendor.hjson
{
  name: "lowrisc_ibex",
  target_dir: "lowrisc_ibex",

  upstream: {
    url: "https://github.com/lowRISC/ibex.git",
    rev: "master",
  },
}
```

This description file essentially says:
We vendor a component called "lowrisc_ibex" and place the code into the "lowrisc_ibex" directory (relative to the description file).
The code comes from the `master` branch of the Git repository found at https://github.com/lowRISC/ibex.git.

With this description file written, the `util/vendor` tool can do its job.

```command
$ cd $REPO_TOP
$ ./util/vendor.py hw/vendor/lowrisc_ibex.vendor.hjson --verbose --update
INFO: Cloning upstream repository https://github.com/lowRISC/ibex.git @ master
INFO: Cloned at revision 7728b7b6f2318fb4078945570a55af31ee77537a
INFO: Copying upstream sources to /home/philipp/src/opentitan/hw/vendor/lowrisc_ibex
INFO: Changes since the last import:
* Typo fix in muldiv: Reminder->Remainder (Stefan Wallentowitz)
INFO: Wrote lock file /home/philipp/src/opentitan/hw/vendor/lowrisc_ibex.lock.hjson
INFO: Import finished
```

Looking at the output, you might wonder: how did the `util/vendor` tool know what changed since the last import?
It knows because it records the commit hash of the last import in a file called the "lock file".
This file can be found along the `.vendor.hjson` file, it's named `.lock.hjson`.

In the example above, it looks roughly like this:

```command
$ cat hw/vendor/lowrisc_ibex.lock.hjson
{
  upstream:
  {
    url: https://github.com/lowRISC/ibex.git
    rev: 7728b7b6f2318fb4078945570a55af31ee77537a
  }
}
```

The lock file should be committed together with the code itself to make the import step reproducible at any time.
This import step can be reproduced by running the `util/vendor` tool without the `--update` flag.

After running `util/vendor`, the code in your local working copy is updated to the latest upstream version.
Next is testing: run simulations, syntheses, or other tests to ensure that the new code works as expected.
Once you're confident that the new code is good to be committed, do so using the normal Git commands.

```command
$ cd $REPO_TOP

$ # Stage all files in the vendored directory
$ git add -A hw/vendor/lowrisc_ibex

$ # Stage the lock file as well
$ git add hw/vendor/lowrisc_ibex.lock.hjson

$ # Now commit everything. Don't forget to write a useful commit message!
$ git commit
```

Instead of running `util/vendor` first, and then manually creating a Git commit, you can also use the `--commit` flag.

```command
$ cd $REPO_TOP
$ ./util/vendor.py hw/vendor/lowrisc_ibex.vendor.hjson \
    --verbose --update --commit
```

This command updates the "lowrisc_ibex" code, and creates a Git commit from it.

Read on for a complete example how to efficiently update a vendored dependency, and how to make changes to such code.

## Update vendored code in our repository

A complete example to update a vendored dependency, commit its changes, and create a pull request from it, is given below.

```command
$ cd $REPO_TOP
$ # Ensure a clean working directory
$ git stash
$ # Create a new branch for the pull request
$ git checkout -b update-ibex-code upstream/master
$ # Update lowrisc_ibex and create a commit
$ ./util/vendor.py hw/vendor/lowrisc_ibex.vendor.hjson \
    --verbose --update --commit
$ # Push the new branch to your fork
$ git push origin update-ibex-code
$ # Restore changes in working directory (if anything was stashed before)
$ git stash pop
```

Now go to the GitHub web interface to open a Pull Request for the `update-ibex-code` branch.

## How to modify vendored code (fix a bug, improve it)

### Step 1: Get the vendored repository

1. Open the vendor description file (`.vendor.hjson`) of the dependency you want to update and take note of the `url` and the `branch` in the `upstream` section.

2. Clone the upstream repository and switch to the used branch:

   ```command
   $ # Go to your source directory (can be anywhere)
   $ cd ~/src
   $ # Clone the repository and switch the branch. Below is an example for ibex.
   $ git clone https://github.com/lowRISC/ibex.git
   $ cd ibex
   $ git checkout master
   ```

After this step you're ready to make your modifications.
You can do so *either* directly in the upstream repository, *or* start in the OpenTitan repository.

### Step 2a: Make modifications in the upstream repository

The easiest option is to modify the upstream repository directly as usual.

### Step 2b: Make modifications in the OpenTitan repository

Most changes to external code are motivated by our own needs.
Modifying the external code directly in the `hw/vendor` directory is therefore a sensible starting point.

1. Make your changes in the OpenTitan repository. Do not commit them.

2. Create a patch with your changes. The example below uses `lowrisc_ibex`.

   ```command
   $ cd hw/vendor/lowrisc_ibex
   $ git diff --relative . > changes.patch
   ```

3. Take note of the revision of the imported repository from the lock file.
   ```command
   $ cat hw/vendor/lowrisc_ibex.lock.hjson | grep rev
    rev: 7728b7b6f2318fb4078945570a55af31ee77537a
   ```

4. Switch to the checked out upstream repository and bring it into the same state as the imported repository.
   Again, the example below uses ibex, adjust as needed.

   ```command
   # Change to the upstream repository
   $ cd ~/src/ibex

   $ # Create a new branch for your patch
   $ # Use the revision you determined in the previous step!
   $ git checkout -b modify-ibex-somehow 7728b7b6f2318fb4078945570a55af31ee77537a
   $ git apply -p1 < $REPO_BASE/hw/vendor/lowrisc_ibex/changes.patch

   $ # Add and commit your changes as usual
   $ # You can create multiple commits with git add -p and committing
   $ # multiple times.
   $ git add -u
   $ git commit
   ```

### Step 3: Get your changes accepted upstream

You have now created a commit in the upstream repository.
Before submitting your changes upstream, rebase them on top of the upstream development branch, typically `master`, and ensure that all tests pass.
Now you need to follow the upstream guidelines on how to get the change accepted.
In many cases their workflow is similar to ours: push your changes to a repository fork on your namespace, create a pull request, work through review comments, and update it until the change is accepted and merged.

### Step 4: Update the vendored copy of the external dependency

After your change is accepted upstream, you can update our copy of the code using the `util/vendor` tool as described before.

## How to vendor new code

Vendoring external code is done by creating a vendor description file, and then running the `util/vendor` tool.

1. Create a vendor description file for the new dependency.
   1. Make note of the Git repository and the branch you want to vendor in.
   2. Choose a name for the external dependency.
      It is recommended to use the format `<vendor>_<name>`.
      Typically `<vendor>` is the lower-cased user or organization name on GitHub, and `<name>` is the lower-cased project name.
   3. Choose a target directory.
      It is recommended use the dependency name as directory name.
   4. Create the vendor description file in `hw/vendor/<vendor>_<name>.vendor.hjson` with the following contents (adjust as needed):

      ```
      // Copyright lowRISC contributors.
      // Licensed under the Apache License, Version 2.0, see LICENSE for details.
      // SPDX-License-Identifier: Apache-2.0
      {
        name: "lowrisc_ibex",
        target_dir: "lowrisc_ibex",

        upstream: {
          url: "https://github.com/lowRISC/ibex.git",
          rev: "master",
        },
      }
      ```

2. Create a new branch for a subsequent pull request

   ```command
   $ git checkout -b vendor-something upstream/master
   ```

3. Commit the vendor description file

   ```command
   $ git add hw/vendor/<vendor>_<name>.vendor.hjson
   $ git commit
   ```

4. Run the `util/vendor` tool for the newly vendored code.

   ```command
   $ cd $REPO_TOP
   $ ./util/vendor.py hw/vendor/lowrisc_ibex.vendor.hjson --verbose --commit
   ```

5. Push the branch to your fork for review (assuming `origin` is the remote name of your fork).

   ```command
   $ git push -u origin vendor-something
   ```

   Now go the GitHub web interface to create a Pull Request for the newly created branch.

## How to exclude some files from the upstream repository

You can exclude files from the upstream code base by listing them in the vendor description file under `exclude_from_upstream`.
Glob-style wildcards are supported (`*`, `?`, etc.), as known from shells.

Example:

```
// section of a .vendor.hjson file
exclude_from_upstream: [
  // exclude all *.h files in the src directory
  "src/*.h",
  // exclude the src_files.yml file
  "src_files.yml",
  // exclude some_directory and all files below it
  "some_directory",
]
```

If you want to add more files to `exclude_from_upstream`, just update this section of the `.vendor.hjson` file and re-run the vendor tool without `--update`.
The repository will be re-cloned without pulling in upstream updates, and the file exclusions and patches specified in the vendor file will be applied.

## How to add patches on top of the imported code

In some cases the upstream code must be modified before it can be used.
For this purpose, the `util/vendor` tool can apply patches on top of imported code.
The patches are kept as separate files in our repository, making it easy to understand the differences to the upstream code, and to switch the upstream code to a newer version.

To apply patches on top of vendored code, do the following:

1. Extend the `.vendor.hjson` file of the dependency and add a `patch_dir` line pointing to a directory of patch files.
   It is recommended to place patches into the `patches/<vendor>_<name>` directory.

    ```
    patch_dir: "patches/lowrisc_ibex",
    ```

2. Place patch files with a `.patch` suffix in the `patch_dir`.

3. When running `util/vendor`, patches are applied on top of the imported code according to the following rules.

   - Patches are applied alphabetical order according to the filename.
     Name patches like `0001-do-someting.patch` to apply them in a deterministic order.
   - Patches are applied relative to the base directory of the imported code.
   - The first directory component of the filename in a patch is stripped, i.e. they are applied with the `-p1` argument of `patch`.
   - Patches are applied with `git apply`, making all extended features of Git patches available (e.g. renames).

If you want to add more patches and re-apply them without updating the upstream repository, add them to the patches directory and re-run the vendor tool without `--update`.

## How to manage patches in a Git repository

Managing patch series on top of code can be challenging.
As the underlying code changes, the patches need to be refreshed to continue to apply.
Adding new patches is a very manual process.
And so on.

Fortunately, Git can be used to simplify this task.
The idea:

- Create a forked Git repository of the upstream code
- Create a new branch in this fork.
- Commit all your changes on top of the upstream code into this branch.
- Convert all commits into patch files and store them where the `util/vendor` tool can find and apply them.

The last step is automated by the `util/vendor` tool through its `--refresh-patches` argument.

1. Modify the vendor description file to add a `patch_repo` section.
   - The `url` parameter specifies the URL to the fork of the upstream repository containing all modifications.
   - The `rev_base` is the base revision, typically the `master` branch.
   - The `rev_patched` is the patched revision, typically the name of the branch with your changes.

    ```
    patch_repo: {
      url: "https://github.com/lowRISC/riscv-dbg.git",
      rev_base: "master",
      rev_patched: "changes",
    },
    ```

2. Create commit and push to the forked repository.
   Make sure to push both branches to the fork: `rev_base` **and** `rev_patched`.
   In the example above, this would be (with `REMOTE_NAME_FORK` being the remote name of the fork):

   ```command
   git push REMOTE_NAME_FORK master changes
   ```

3. Run the `util/vendor` tool with the `--refresh-patches` argument.
   It will first check out the patch repository and convert all commits which are in the `rev_patched` branch and not in the `rev_base` branch into patch files.
   These patch files are then stored in the patch directory.
   After that, the vendoring process continues as usual: changes from the upstream repository are downloaded if `--update` passed, all patches are applied, and if instructed by the `--commit` flag, a commit is created.
   This commit now also includes the updated patch files.

To update the patches you can use all the usual Git tools in the forked repository.

- Use `git rebase` to refresh them on top of changes in the upstream repository.
- Add new patches with commits to the `rev_patched` fork.
- Remove patches or reorder them with Git interactive rebase (`git rebase -i`).

It is important to update and push *both* branches in the forked repository: the `rev_base` branch and the `rev_patched` branch.
Use `git log rev_base..rev_patched` (replace `rev_base` and `rev_patched` as needed) to show all commits which will be turned into patches.
