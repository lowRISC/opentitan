# Configuration file for the Sphinx documentation builder.
#
# This file only contains a selection of the most common options. For a full
# list see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Path setup --------------------------------------------------------------

# If extensions (or modules to document with autodoc) are in another directory,
# add these directories to sys.path here. If the directory is relative to the
# documentation root, use os.path.abspath to make it absolute, like shown here.
#
# import os
# import sys
# sys.path.insert(0, os.path.abspath('.'))
from pallets_sphinx_themes import ProjectLink
import sphinx_rtd_theme

# -- Project information -----------------------------------------------------

project = 'riscv-dv'
copyright = '2020, Google, Inc.'
author = 'Google, Inc.'


# -- General configuration ---------------------------------------------------

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
master_doc = "index"
extensions = [
    "sphinx.ext.autodoc",
    "sphinx.ext.intersphinx",
    "pallets_sphinx_themes",
    "sphinxcontrib.log_cabinet",
    "sphinx_issues",
    "rst2pdf.pdfbuilder",
    'sphinx_rtd_theme',
]

# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This pattern also affects html_static_path and html_extra_path.
exclude_patterns = []


# -- Options for HTML output -------------------------------------------------

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
#
html_theme = "sphinx_rtd_theme"
#html_theme_options = {"index_sidebar_logo": False}
#
#html_context = {
#    "project_links": [
#        ProjectLink("Source Code", "https://github.com/google/riscv-dv.git"),
#        ProjectLink("Issue Tracker", "https://github.com/google/riscv-dv/issues"),
#    ]
#}
#
#html_sidebars = {
#    "index": ["project.html", "localtoc.html", "searchbox.html"],
#    "**": ["localtoc.html", "relations.html", "searchbox.html"],
#}

# -- For PDF output ---------------------------------------------------------
pdf_documents = [('index', u'riscv-dv', u'RISCV-DV', u'Google, Inc'),]

