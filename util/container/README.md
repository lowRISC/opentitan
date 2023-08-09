# Docker Container

Docker container based on Ubuntu 20.04 LTS containing various hardware and
software development tools for OpenTitan, as listed in the
[OpenTitan documentation](../../doc/guides/getting_started/src/README.md).

## Local Build Instructions

For now, no pre-built containers are available; you'll need to build the Docker container locally.
First, you'll need to install Docker either through your package manager or their [download page](https://www.docker.com/get-started/).
You'll also need to clone the [OpenTitan repository](https://github.com/lowRISC/opentitan) if you haven't done that yet.
Then, from `$REPO_TOP` (the top-level directory in the repository, called `opentitan` by default), you can build the container with:

```shell
$ sudo docker build -t opentitan -f util/container/Dockerfile .
```

## Using the Container

Run the container with `docker run`, mapping the current working directory to
`/home/dev/src`. The user `dev` will have the same user ID as the current user
on the host (you!), causing all files created by the `dev` user in the container
to be owned by the current user on the host.

If you'd like to initialize your shell environment in a specific way, you can
pass an environment variable `USER_CONFIG=/path/to/a/script.sh`. Otherwise,
remove the `--env USER_CONFIG` argument from the invocation shown below.

The script passed through this mechanism will be sourced. The path of the script
must be within the container, e.g. in the OpenTitan repository directory.

```
docker run -t -i \
  -v $(pwd):/home/dev/src \
  --env DEV_UID=$(id -u) --env DEV_GID=$(id -g) \
  --env USER_CONFIG=/home/dev/src/docker-user-config.sh \
  opentitan:latest \
  bash
```

You can use `sudo` within the container to gain root permissions.
