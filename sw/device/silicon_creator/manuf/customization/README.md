# Personalization Firmware Extensions

The personalization firmware `ft_personalize.c` defines an `extern` extension
function that is invoked as the final step in the personalization flow.

`status_t personalize_extension(ujson_t *uj)`

The example function provided in this example external Bazel repo does nothing,
except print a message to the console. However, this provides a mechanism for
SKU owners / customers to develop closed-source personalization FW extensions,
that can easily make use of open-source code.

This feature is implemented with the help of some custom Bazel repository rules.
Specifically, in this directory we define a secondary Bazel
repository (`@perso_exts`) that is designed to be used in
conjunction with the main OpenTitan Bazel repository. Within this repository, we
define a single `perso_ext` library that is linked with the reference
`ft_personalize` binary. The `perso_ext` library itself just contains an
implementation of the `personalize_extension(...)` function described above.
However, the `perso_ext` library is linked with other libraries
based on a Bazel `config_setting` that allows you to toggle which personalize
extension library should be used (if you are building binaries for several SKU
owners).

Note, the Bazel configuration settings and example personalization extension
library (`perso_ext`) provided in this
repository are merely examples, as the `personalize_extension(...)` function
implemented does nothing, except print a message.
