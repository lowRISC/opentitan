---
title: "Building documentation"
---

The documentation for OpenTitan is available [online](https://docs.opentitan.org).
The creation of documentation is mainly based around the conversion from Markdown to HTML files with [Hugo](https://gohugo.io/).
Rules for how to write correct Markdown files can be found in the [reference manual]({{< relref "doc/rm/markdown_usage_style.md" >}}).

## Building locally

Before Hugo is executed a few project specific processing steps are necessary.
These steps require the installation of the dependencies outlined in the following section.
All processing steps as well as the invocation to Hugo are combined in the script `util/build_docs.py`.

### Prerequisites

Install the required tools by running the following command from the repository root.

```console
$ sudo apt install curl python3 python3-pip
$ pip3 install --user -r python-requirements.txt
```

### Running the server

In order to run a local instance of the documentation server run the following command from the root of the project repository.

```console
$ ./util/build_docs.py --preview
```

This will execute the preprocessing, fetch the correct Hugo version, build the documentation and finally start a local server.
The output will indicate at which address the local instance can be accessed.
The default is [http://127.0.0.1:1313](http://127.0.0.1:1313).
