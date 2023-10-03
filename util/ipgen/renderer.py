# Copyright lowRISC contributors.
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

_HJSON_LICENSE_HEADER = ("""// Copyright lowRISC contributors.
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
                if template_param.param_type == 'string':
                    val_typed = str(val)  # type: Union[int, str, object]
                elif template_param.param_type == 'int':
                    if not isinstance(val, int):
                        val_typed = int(val, 0)
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
        template_vlnv = template_vlnv_str.split(':')
        if len(template_vlnv) != 3 and len(template_vlnv) != 4:
            raise TemplateRenderError(
                f"{template_vlnv_str} isn't a valid FuseSoC VLNV. "
                "Required format: 'vendor:library:name[:version]'")
        template_core_name = template_vlnv[2]
        template_core_version = (template_vlnv[3]
                                 if len(template_vlnv) == 4 else None)

        # Remove the template name from the start of the core name.
        # For example, a core name `rv_plic_component` will result in an
        # instance name 'my_instance_component' (instead of
        # 'my_instance_rv_plic_component').
        if "module_instance_name" in self.ip_config.param_values:
            assert template_core_name.startswith(
                self.ip_config.param_values["module_instance_name"])
            idx = len(self.ip_config.param_values["module_instance_name"])
            template_core_name = template_core_name[idx:]
        elif template_core_name.startswith(self.ip_template.name):
            template_core_name = template_core_name[len(self.ip_template.name
                                                        ):]

        instance_core_name = self.ip_config.instance_name + template_core_name
        instance_vlnv = ['lowrisc', 'opentitan', instance_core_name]

        # Keep the version component if it was present before.
        if template_core_version is not None:
            instance_vlnv.append(template_core_version)

        return ':'.join(instance_vlnv)

    def _render_mako_template_to_str(self, template_filepath: Path) -> str:
        """ Render a template and return the rendered text. """

        lookup = self._get_mako_template_lookup()
        template_filepath_rel = template_filepath.relative_to(
            self.ip_template.template_path)
        template = lookup.get_template(str(template_filepath_rel))

        helper_funcs = {}
        helper_funcs['instance_vlnv'] = self._tplfunc_instance_vlnv

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

    The IP description is the content of what is typically stored
    data/ip_name.hjson.
    """

    def render(self) -> str:
        template_path = self.ip_template.template_path

        # Look for a data/ip_name.hjson.tpl template file and render it.
        hjson_tpl_path = template_path / 'data' / (self.ip_template.name +
                                                   '.hjson.tpl')
        if hjson_tpl_path.is_file():
            return self._render_mako_template_to_str(hjson_tpl_path)

        # Otherwise, if a data/ip_name.hjson file exists, use that.
        hjson_path = template_path / 'data' / (self.ip_template.name +
                                               '.hjson')
        try:
            with open(hjson_path, 'r') as f:
                return f.read()
        except FileNotFoundError:
            raise TemplateRenderError(
                f"Neither a IP description template at {hjson_tpl_path}, "
                f"nor an IP description at {hjson_path} exist!")


class IpBlockRenderer(IpTemplateRendererBase):
    """ Produce a full IP block directory from a template.

    - Copy everything but Mako templates (files ending with '.tpl') into the
      destination directory.
    - Process all Mako templates and write the results to the output directory.
      A template at <PATH>.tpl will write results to <PATH> in the output
      directory.
    - Run reggen to generate the register interface.
    """

    def render(self, output_dir: Path, overwrite_output_dir: bool) -> None:
        """ Render the IP template into output_dir. """

        # Ensure that we operate on an absolute path for output_dir.
        output_dir = output_dir.resolve()

        if not overwrite_output_dir and output_dir.exists():
            raise TemplateRenderError(
                "Output directory '{}' exists and should not be overwritten.".
                format(output_dir))

        # Prepare the IP directory in a staging area to later atomically move it
        # to the final destination.
        output_dir_staging = output_dir.parent / f".~{output_dir.stem}.staging"
        if output_dir_staging.is_dir():
            raise TemplateRenderError(
                f"Output staging directory '{output_dir_staging}' already "
                "exists. Remove it and try again.")

        template_path = self.ip_template.template_path

        try:
            # Copy everything but the templates and the template description.
            ignore = shutil.ignore_patterns('*.tpl', '*.tpldesc.hjson')
            shutil.copytree(template_path, output_dir_staging, ignore=ignore)

            # Render templates.
            for template_filepath in template_path.glob('**/*.tpl'):
                template_filepath_rel = template_filepath.relative_to(
                    template_path)

                # Put the output file into the same relative directory as the
                # template. The output file will also have the same name as the
                # template, just without the '.tpl' suffix.
                outdir_path = output_dir_staging / template_filepath_rel.parent

                self._render_mako_template_to_file(template_filepath,
                                                   outdir_path)

            # Generate register interface through reggen.
            hjson_path = (output_dir_staging / 'data' /
                          (self.ip_template.name + '.hjson'))
            if "module_instance_name" in self.ip_config.param_values:
                hjson_path = (
                    output_dir_staging / 'data' /
                    self.ip_config.param_values["module_instance_name"] +
                    '.hjson')
            if not hjson_path.exists():
                raise TemplateRenderError(
                    "Invalid template: The IP description file "
                    f"{str(hjson_path)!r} does not exist.")
            rtl_path = output_dir_staging / 'rtl'
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
                output_dir_staging / 'data' /
                f'{self.ip_config.instance_name}.ipconfig.hjson',
                header=_HJSON_LICENSE_HEADER)

            # Safely overwrite the existing directory if necessary:
            #
            # - First move the existing directory out of the way.
            # - Then move the staging directory with the new content in place.
            # - Finally remove the old directory.
            #
            # If anything goes wrong in the meantime we are left with either
            # the old or the new directory, and potentially some backups of
            # outdated files.
            do_overwrite = overwrite_output_dir and output_dir.exists()
            output_dir_existing_bak = output_dir.with_suffix(
                '.bak~' + str(int(time.time())))
            if do_overwrite:
                os.rename(output_dir, output_dir_existing_bak)

            # Move the staging directory to the final destination.
            os.rename(output_dir_staging, output_dir)

            # Remove the old/"overwritten" data.
            if do_overwrite:
                try:
                    shutil.rmtree(output_dir_existing_bak)
                except Exception as e:
                    msg = (
                        'Unable to delete the backup directory '
                        f'{output_dir_existing_bak} of the overwritten data. '
                        'Please remove it manually.')
                    raise TemplateRenderError(msg).with_traceback(
                        e.__traceback__)

        except TemplateRenderError as e:
            log.error(f'{e!s}')
            raise

        finally:
            # Ensure that the staging directory is removed at the end. Ignore
            # errors as the directory should not exist at this point actually.
            shutil.rmtree(output_dir_staging, ignore_errors=True)
