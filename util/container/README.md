# Docker Container

Docker container based on Ubuntu 18.04 LTS containing various hardware and
software development tools for OpenTitan, as listed in the
[OpenTitan documentation](https://docs.opentitan.org/doc/ug/install_instructions/).

## Local Build Instructions

Skip this step if planning to use the pre-built container. To build in local
mode:
<!-- TODO: Where can one find the pre-built container mentioned above? --->

```shell
$ cd $REPO_TOP
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
