# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging
import os
import shutil
import time
from pathlib import Path
from typing import Dict, Optional, Union

import reggen.gen_rtl
from mako import exceptions as mako_exceptions  # type: ignore
from mako.lookup import TemplateLookup as MakoTemplateLookup  # type: ignore
from reggen.countermeasure import CounterMeasure
from reggen.ip_block import IpBlock

from .lib import IpConfig, IpTemplate, TemplateParameter, TemplateRenderError

_HJSON_LICENSE_HEADER = ("""// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
""")

log = logging.getLogger(__name__)


class IpTemplateRendererBase:
    """ Render an IpTemplate into an IP block. """

    ip_template: IpTemplate
    ip_config: IpConfig

    _lookup: Optional[MakoTemplateLookup] = None

    def __init__(self, ip_template: IpTemplate, ip_config: IpConfig) -> None:
        self.ip_template = ip_template
        self.ip_config = ip_config
        self._check_param_values()

    def _check_param_values(self) -> None:
        """ Check if all parameters in IpConfig are defined in the template. """

        for name in self.ip_config.param_values:
            if name not in self.ip_template.params:
                raise KeyError(f"No parameter named {name!r} exists.")

    def get_template_parameter_values(
            self) -> Dict[str, Union[str, int, object]]:
        """ Get a typed mapping of all template parameters and their values.
        """
        ret = {}

        for name, template_param in self.ip_template.params.items():
            if name in self.ip_config.param_values:
                val = self.ip_config.param_values[name]
            else:
                log.info(f"Using default value for template parameter {name}")
                val = template_param.default

            assert template_param.param_type in TemplateParameter.VALID_PARAM_TYPES
            try:
                val_typed: Union[bool, int, str, object] = None
                if template_param.param_type == 'string':
                    val_typed = str(val)
                elif template_param.param_type == 'int':
                    if not isinstance(val, int):
                        val_typed = int(val, 0)
                    else:
                        val_typed = val
                elif template_param.param_type == 'bool':
                    if not isinstance(val, bool):
                        val_typed = bool(val, False)
                    else:
                        val_typed = val
                elif template_param.param_type == 'object':
                    val_typed = val
            except (ValueError, TypeError):
                raise TemplateRenderError(
                    f"For parameter {name} cannot convert value {val!r} "
                    f"to {template_param.param_type}.") from None

            ret[name] = val_typed

        return ret

    def _get_mako_template_lookup(self) -> MakoTemplateLookup:
        """ Get a Mako TemplateLookup object """

        if self._lookup is None:
            # Define the directory containing the IP template as "base"
            # directory, allowing templates to include other templates within
            # this directory using relative paths.
            # Use strict_undefined to throw a NameError if undefined variables
            # are used within a template.
            self._lookup = MakoTemplateLookup(
                directories=[str(self.ip_template.template_path)],
                strict_undefined=True)
        return self._lookup

    def _tplfunc_instance_vlnv(self, template_vlnv_str: str) -> str:
        """Makes a vlnv into an instance specific one.

        A vlnv is a string of the form vendor:library:name[:version] where
        the version is optional. This is transformed as follows:
        - The vendor string becomes `lowrisc`.
        - The library string becomes `opentitan`.
        - The name is processed as follows:
          - If the `module_instance_name` parameter exists, the name must start
            with it as a prefix, and that is replaced by the `instance_name`
            value.
          - If the name starts with the template name, it is replaced by the
            `instance_name` value.
          - Otherwise the `instance_name` is prefixed to the name.
        - The optional version is preserved.

        Raises exceptions for malformed vlnvs.
        """
        template_vlnv = template_vlnv_str.split(':')
        if len(template_vlnv) != 3 and len(template_vlnv) != 4:
            raise TemplateRenderError(
                f"{template_vlnv_str} isn't a valid FuseSoC VLNV. "
                "Required format: 'vendor:library:name[:version]'")
        template_core_name = template_vlnv[2]
        template_core_version = (template_vlnv[3]
                                 if len(template_vlnv) == 4 else None)

        if "module_instance_name" in self.ip_config.param_values:
            if not template_core_name.startswith(
                    self.ip_config.param_values["module_instance_name"]):
                raise TemplateRenderError(
                    f'The name field in {template_vlnv_str} must start with '
                    f'{self.ip_config.param_values["module_instance_name"]}')
            idx = len(self.ip_config.param_values["module_instance_name"])
            template_core_name = template_core_name[idx:]
        elif template_core_name.startswith(self.ip_template.name):
            template_core_name = template_core_name[len(self.ip_template.name
                                                        ):]

        instance_core_name = self.ip_config.instance_name + template_core_name
        instance_vlnv = ['lowrisc', 'opentitan', instance_core_name]

        if template_core_version is not None:
            instance_vlnv.append(template_core_version)

        return ':'.join(instance_vlnv)

    def _render_mako_template_to_str(self, template_filepath: Path) -> str:
        """ Render a template and return the rendered text. """

        lookup = self._get_mako_template_lookup()
        template_filepath_rel = template_filepath.relative_to(
            self.ip_template.template_path)
        template = lookup.get_template(str(template_filepath_rel))

        helper_funcs = {'instance_vlnv': self._tplfunc_instance_vlnv}

        # TODO: Introduce namespacing for the template parameters and other
        # parameters, and/or pass the IpConfig instance to the template after
        # we have converted more IP blocks to ipgen.
        tpl_args = {
            "instance_name": self.ip_config.instance_name,  # type: ignore
            **helper_funcs,  # type: ignore
            **self.get_template_parameter_values()  # type: ignore
        }
        try:
            return template.render(**tpl_args)
        except Exception:
            raise TemplateRenderError(
                "Unable to render template: " +
                mako_exceptions.text_error_template().render(),
                self.get_template_parameter_values()) from None

    def _render_mako_template_to_file(self, template_filepath: Path,
                                      outdir_path: Path) -> None:
        """ Render a file template into a file in outdir_path.

        The name of the output file matches the file name of the template file,
        without the '.tpl' suffix.
        """

        assert outdir_path.is_dir()

        outfile_name = self._filename_without_tpl_suffix(template_filepath)

        rendered_str = self._render_mako_template_to_str(template_filepath)
        try:
            with open(outdir_path / outfile_name, 'w') as f:
                f.write(rendered_str)
        except OSError as e:
            raise TemplateRenderError(
                f'Cannot write to {outdir_path / outfile_name!s}: {e!s}')

    def _filename_without_tpl_suffix(self, filepath: Path) -> str:
        """ Get the name of the file without a '.tpl' suffix. """
        assert filepath.suffix == '.tpl'
        filename = filepath.stem
        if "module_instance_name" in self.ip_config.param_values:
            filename = self.ip_config.param_values[
                "module_instance_name"] + filename[len(self.ip_template.name):]
        return filename


class IpDescriptionOnlyRenderer(IpTemplateRendererBase):
    """ Generate the IP description only.

    The IP description must be at data/ip_name.hjson.tpl.
    """

    def render(self) -> str:
        """Renders template file at data/ip_name.hjson.tpl as a string.

        Raises an exception if the file is not found.
        """
        hjson_tpl_path = (self.ip_template.template_path / 'data' /
                          f'{self.ip_template.name}.hjson.tpl')
        if hjson_tpl_path.is_file():
            return self._render_mako_template_to_str(hjson_tpl_path)

        raise TemplateRenderError(
            f"No IP description template at {hjson_tpl_path}")


class IpBlockRenderer(IpTemplateRendererBase):
    """ Produce a full IP block directory from a template.

    - Copy everything but Mako templates (files ending with '.tpl') into the
      destination directory.
    - Process all Mako templates and write the results to the output directory.
      A template at <PATH>.tpl will write results to <PATH> in the output
      directory.
    - Run reggen to generate the register interface.
    """

    def _refresh_directory(self, staging_dir: Path, output_dir: Path,
                           overwrite_output_dir: bool) -> None:
        """Safely overwrite the existing directory if necessary.

        The staging directory contains the newly generated contents.
        - First move the existing directory out of the way.
        - Then move the staging directory in place.
        - Finally remove the old directory.

        If anything goes wrong in the meantime we are left with either
        the old or the new directory, and potentially some backups of
        outdated files.

        Raises exceptions if any of the file operations fails.
        """
        do_overwrite = overwrite_output_dir and output_dir.exists()
        output_dir_existing_bak = output_dir.with_suffix(
            '.bak~' + str(int(time.time())))
        if do_overwrite:
            try:
                os.rename(output_dir, output_dir_existing_bak)
            except OSError as e:
                msg = (f'Cannot move existing directory {output_dir} to '
                       f'{output_dir_existing_bak}.')
                raise TemplateRenderError(msg).with_traceback(
                    e.__traceback__)

        try:
            os.rename(staging_dir, output_dir)
        except OSError as e:
            msg = (f'Cannot move staging directory {staging_dir} to '
                   f'{output_dir}.')
            raise TemplateRenderError(msg).with_traceback(e.__traceback__)

        if do_overwrite:
            try:
                shutil.rmtree(output_dir_existing_bak)
            except Exception as e:
                msg = (
                    'Unable to delete the backup directory '
                    f'{output_dir_existing_bak} of the overwritten data. '
                    'Please remove it manually.')
                raise TemplateRenderError(msg).with_traceback(e.__traceback__)

    def render(self, output_dir: Path, overwrite_output_dir: bool) -> None:
        """ Render the IP template into output_dir.

        Generates the IP directory in a staging area and atomically moves it
        to the final destination if generation succeeds. Generation is done in
        stages:
        - Copy all non-template files.
        - Render all *.tpl files to their corresponding location.
        - Generate register file description with reggen.
        """
        # Ensure to operate on an absolute path for output_dir.
        output_dir = output_dir.resolve()

        if not overwrite_output_dir and output_dir.exists():
            raise TemplateRenderError(
                "Output directory '{}' exists and should not be overwritten.".
                format(output_dir))

        staging_dir = output_dir.parents[0] / f".~{output_dir.stem}.staging"
        if staging_dir.is_dir():
            raise TemplateRenderError(
                f"Output staging directory '{staging_dir}' already exists: "
                "remove it and try again.")

        template_path = self.ip_template.template_path

        try:
            # Copy everything but the templates and the template description.
            ignore = shutil.ignore_patterns('*.tpl', '*.tpldesc.hjson')
            shutil.copytree(template_path, staging_dir, ignore=ignore)
        except shutil.Error as e:
            log.error(f'Error copying non-template files: {e}')
            raise TemplateRenderError("Error copying non-template files: {e}")

        # Render templates.
        try:
            for template_filepath in template_path.glob('**/*.tpl'):
                template_filepath_rel = template_filepath.relative_to(
                    template_path)

                # Put the output file into the same relative directory as the
                # template. The output file will also have the same name as the
                # template, just without the '.tpl' suffix.
                outdir_path = staging_dir / template_filepath_rel.parent

                self._render_mako_template_to_file(template_filepath,
                                                   outdir_path)
        except Exception:
            shutil.rmtree(staging_dir, ignore_errors=True)
            raise

        hjson_base_name = self.ip_config.param_values.get(
            "module_instance_name", self.ip_template.name)

        # Generate register interface through reggen.
        hjson_path = staging_dir / 'data' / f'{hjson_base_name}.hjson'

        if not hjson_path.exists():
            raise TemplateRenderError(
                "Invalid template: The IP description file "
                f"{str(hjson_path)!r} does not exist. "
                "Inspect the {staging_dir} directory.")

        rtl_path = staging_dir / 'rtl'
        rtl_path.mkdir(exist_ok=True)

        obj = IpBlock.from_path(str(hjson_path), [])

        # If this block has countermeasures, we grep for RTL annotations in
        # all .sv implementation files and check whether they match up
        # with what is defined inside the Hjson.
        sv_files = rtl_path.glob('*.sv')
        rtl_names = CounterMeasure.search_rtl_files(sv_files)
        obj.check_cm_annotations(rtl_names, str(hjson_path))

        # TODO: Pass on template parameters to reggen? Or enable the user
        # to set a different set of parameters in the renderer?
        reggen.gen_rtl.gen_rtl(obj, str(rtl_path))

        # Write IP configuration (to reproduce the generation process).
        # TODO: Should the ipconfig file be written to the instance name,
        # or the template name?
        self.ip_config.to_file(
            staging_dir / 'data' /
            f'{self.ip_config.instance_name}.ipconfig.hjson',
            header=_HJSON_LICENSE_HEADER)

        self._refresh_directory(staging_dir, output_dir,
                                overwrite_output_dir)

        # Ensure that the staging directory is removed at the end. Ignore
        # errors as the directory should not exist at this point actually.
        shutil.rmtree(staging_dir, ignore_errors=True)
