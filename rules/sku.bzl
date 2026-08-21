# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

SkuCertInfo = provider(
    doc = "Information about a certificate for SKU configuration",
    fields = {
        "certificate": "File: The certificate PEM file",
        "key": "File or String: The key file or key ID string",
        "key_is_file": "Bool: True if key is a file",
        "key_file": "File: The key file (if key_is_file is True)",
        "key_type": "String: 'Token' or 'Raw'",
        "key_id": "String: The key ID",
    },
)

def _sku_cert_impl(ctx):
    key_value = None
    key_is_file = ctx.attr.key_file != None
    runfiles_files = [ctx.file.certificate]

    if ctx.attr.key and ctx.attr.key_file:
        fail("Only one of 'key' or 'key_file' can be set")
    elif ctx.attr.key:
        key_value = ctx.attr.key
    elif ctx.attr.key_file:
        key_value = ctx.file.key_file.short_path
        runfiles_files.append(ctx.file.key_file)
    else:
        fail("One of 'key' or 'key_file' must be set")

    return [
        SkuCertInfo(
            certificate = ctx.file.certificate,
            key = key_value,
            key_is_file = key_is_file,
            key_file = ctx.file.key_file,
            key_type = ctx.attr.key_type,
            key_id = ctx.attr.key_id,
        ),
        DefaultInfo(
            runfiles = ctx.runfiles(files = runfiles_files),
        ),
    ]

sku_cert = rule(
    implementation = _sku_cert_impl,
    attrs = {
        "certificate": attr.label(allow_single_file = True, mandatory = True),
        "key": attr.string(),
        "key_file": attr.label(allow_single_file = True),
        "key_type": attr.string(values = ["Raw", "Token"], mandatory = True),
        "key_id": attr.string(mandatory = True),
    },
)

def _sku_cfg_impl(ctx):
    config = {
        "name": ctx.attr.sku_name,
        "product": ctx.attr.product,
        "si_creator": ctx.attr.si_creator,
        "package": ctx.attr.package,
        "target_lc_state": ctx.attr.target_lc_state,
        "otp": ctx.attr.otp,
    }

    if ctx.attr.owner_fw_boot_str:
        config["owner_fw_boot_str"] = ctx.attr.owner_fw_boot_str

    runfiles_files = []

    def process_ca(cert_dep):
        if not cert_dep:
            return None
        info = cert_dep[SkuCertInfo]
        ca_config = {
            "certificate": info.certificate.short_path,
            "key_type": info.key_type,
            "key_id": info.key_id,
            "key": info.key,
        }
        runfiles_files.append(info.certificate)
        if info.key_is_file:
            runfiles_files.append(info.key_file)
        return ca_config

    if ctx.attr.dice_ca:
        config["dice_ca"] = process_ca(ctx.attr.dice_ca)
    if ctx.attr.ext_ca:
        config["ext_ca"] = process_ca(ctx.attr.ext_ca)

    if ctx.attr.token_encrypt_key:
        token_key_file = ctx.file.token_encrypt_key
        config["token_encrypt_key"] = token_key_file.short_path
        runfiles_files.append(token_key_file)

    if ctx.files.perso_bins:
        perso_files = ctx.files.perso_bins

        def get_dir(file):
            parts = file.short_path.split("/")
            return "/".join(parts[:-1])

        first_dir = get_dir(perso_files[0])
        for f in perso_files[1:]:
            d = get_dir(f)
            if d != first_dir:
                fail("All files in perso_bins must be in the same directory. Expected: {}, got {} for {}".format(first_dir, d, f.short_path))

        if first_dir:
            perso_bin_path = first_dir + "/" + ctx.attr.perso_bin_suffix
        else:
            perso_bin_path = ctx.attr.perso_bin_suffix

        config["perso_bin"] = perso_bin_path
        runfiles_files.extend(perso_files)

    output_json = ctx.actions.declare_file(ctx.label.name + ".json")

    ctx.actions.write(
        output = output_json,
        content = json.encode(config),
    )

    return [
        DefaultInfo(
            files = depset([output_json]),
            runfiles = ctx.runfiles(files = runfiles_files),
        ),
    ]

sku_cfg = rule(
    implementation = _sku_cfg_impl,
    attrs = {
        "sku_name": attr.string(mandatory = True),
        "product": attr.string(mandatory = True),
        "si_creator": attr.string(mandatory = True),
        "package": attr.string(mandatory = True),
        "target_lc_state": attr.string(values = ["dev", "prod", "prod_end"], mandatory = True),
        "otp": attr.string(mandatory = True),
        "owner_fw_boot_str": attr.string(),
        "dice_ca": attr.label(providers = [SkuCertInfo]),
        "ext_ca": attr.label(providers = [SkuCertInfo]),
        "token_encrypt_key": attr.label(allow_single_file = True),
        "perso_bins": attr.label_list(allow_files = True),
        "perso_bin_suffix": attr.string(),
    },
)
