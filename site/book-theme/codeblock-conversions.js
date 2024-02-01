// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

function convert_codeblocks() {
  let replace_codeblock = (query, template_fn) => {
    for (let instance of document.querySelectorAll(query)) {
      let new_node = template_fn();
      new_node.innerHTML = instance.innerHTML;
      instance.parentElement.replaceWith(new_node);
    };
  };
  replace_codeblock(".language-mermaid", () => {
    let template = document.createElement("pre");
    template.classList.add("mermaid");
    return template;
  });
  replace_codeblock(".language-wavejson", () => {
    let template = document.createElement("script");
    template.type = "WaveDrom";
    return template;
  });
}
convert_codeblocks();
window.addEventListener('load', WaveDrom.ProcessAll)
