def _mass_storage_flash_impl(ctx):
    script_template = """
STLINK_MASS_STORAGE=/media/$USER/STLINK_V3S
if [ -d  $STLINK_MASS_STORAGE ]; then
    cp {firmware} $STLINK_MASS_STORAGE/firmware.bin

    # Wait for st-link to disconnect
    echo Uploading
    while [ -d $STLINK_MASS_STORAGE ]; do
        sleep 1
        printf .
    done
    # Wait for st-link to reconnect 
    while [ ! -d $STLINK_MASS_STORAGE ]; do
        sleep 1
        printf .
    done
    echo done

    # Check if upload was succesful
    if [ -f $STLINK_MASS_STORAGE/FAIL.TXT ]; then
        echo "Failed to upload"
        cat  $STLINK_MASS_STORAGE/FAIL.TXT
        exit 1
    fi
else
    echo "STLINK_V3S not connected" 
    exit 1
fi
"""
    script = ctx.actions.declare_file("%s.sh" % ctx.label.name)
    script_content = script_template.format(
        firmware = ctx.file.image.short_path,
    )
    ctx.actions.write(script, script_content, is_executable = True)
    runfiles = ctx.runfiles(files = [ctx.file.image])
    return [DefaultInfo(executable = script, runfiles = runfiles)]

mass_storage_flash = rule(
    _mass_storage_flash_impl,
    attrs = {
        "image": attr.label(
            doc = "Binary image to flash",
            mandatory = True,
            allow_single_file = True,
        ),
    },
    executable = True,
)
