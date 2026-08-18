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
    if len(ctx.attr.dice_mldsa_certs_from_device) > 0:
        config["dice_mldsa_certs_from_device"] = ctx.attr.dice_mldsa_certs_from_device
        if not ctx.attr.dice_mldsa_ca:
            fail("No DICE CA configuration provided to endorse ML-DSA " +
                 "certificates when such certificates are expected from the " +
                 "device during provisioning")
        config["dice_mldsa_ca"] = process_ca(ctx.attr.dice_mldsa_ca)

        for cert_name in ctx.attr.dice_mldsa_certs_to_device:
            if cert_name not in ctx.attr.dice_mldsa_certs_from_device:
                fail("Endorsed ML-DSA certificate {} expected to be sent to " +
                     "the device, but not present in list of certificates " +
                     "expected from device during provisioning ({})".format(
                         cert_name,
                         ctx.attr.dice_mldsa_certs_from_device,
                     ))
        config["dice_mldsa_certs_to_device"] = ctx.attr.dice_mldsa_certs_to_device

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

    if ctx.files.scrambling_bins:
        scrambling_files = ctx.files.scrambling_bins

        def get_scrambling_dir(file):
            parts = file.short_path.split("/")
            return "/".join(parts[:-1])

        first_scrambling_dir = get_scrambling_dir(scrambling_files[0])
        for f in scrambling_files[1:]:
            d = get_scrambling_dir(f)
            if d != first_scrambling_dir:
                fail("All files in scrambling_bins must be in the same directory.")

        if first_scrambling_dir:
            scrambling_bin_path = first_scrambling_dir + "/" + ctx.attr.scrambling_bin_suffix
        else:
            scrambling_bin_path = ctx.attr.scrambling_bin_suffix

        config["scrambling_bin"] = scrambling_bin_path
        runfiles_files.extend(scrambling_files)

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
        # Optional. Only used (and required) when building for configurations
        # with MLDSA support
        "dice_mldsa_ca": attr.label(
            providers = [SkuCertInfo],
            doc = "CA configuration to use to endorse ML-DSA TBS certificates" +
                  " from device, if ML-DSA provisioning support is enabled",
        ),
        "dice_mldsa_certs_from_device": attr.string_list(
            doc = "List of TBS certificate names to expect from the device " +
                  "when doing provisioning with ML-DSA support. All of these " +
                  "will be endorsed during provisioning",
        ),
        "dice_mldsa_certs_to_device": attr.string_list(
            doc = "List of ML-DSA endorsed certificate names to send back to " +
                  "the device when ML-DSA provisioning support is enabled. " +
                  "This must be a subset of `dice_mldsa_certs_from_device`. " +
                  "These certificates will be included in the final hash " +
                  "that the host tool expects back from the device for " +
                  "certificates it writes to internal flash",
        ),
        "ext_ca": attr.label(providers = [SkuCertInfo]),
        "token_encrypt_key": attr.label(allow_single_file = True),
        "perso_bins": attr.label_list(allow_files = True),
        "perso_bin_suffix": attr.string(),
        "scrambling_bins": attr.label_list(allow_files = True),
        "scrambling_bin_suffix": attr.string(),
    },
)
