// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class LowriscBlock extends HTMLElement {
  static observedAttributes = ["pos", "center"];

  #observer = null;

  constructor() {
    super();
    this.#observer = new ResizeObserver(() => this.update());
  }

  attributeChangedCallback() {
    this.update();
  }

  connectedCallback() {
    this.update();
    this.#observer.observe(this);
  }

  disconnectedCallback() {
    this.#observer.disconnect();
  }

  setCssVariable(name, value) {
    this.style[value ? "setProperty" : "removeProperty"](name, value);
  }

  update() {
    this.classList.add("lowrisc-block");

    const [x, y, w, h] = (this.getAttribute("pos") || "0").split(/\s+/);

    this.setCssVariable("--block-top", y);
    this.setCssVariable("--block-left", x);
    this.setCssVariable("--block-width", w);
    this.setCssVariable("--block-height", h);

    const center = this.getAttribute("center") || "";
    this.setCssVariable("--offset-top", center.includes("y") && h ? - h / 2 : 0);
    this.setCssVariable("--offset-left", center.includes("x") && w ? - w / 2 : 0);
  }
}

customElements.define('lowrisc-block', LowriscBlock);

class LowriscCrossbar extends LowriscBlock {
  static observedAttributes = [...super.observedAttributes, "length"];

  #container = null;

  connectedCallback() {
    this.#container = this.#container || document.createElement("div");
    this.#container.classList.add("crossbar-background");
    this.appendChild(this.#container);

    super.connectedCallback();
  }

  update() {
    super.update();
    this.classList.add("lowrisc-crossbar");

    if (!this.#container) return;

    const [s, e] = (this.getAttribute("length") || "").split(/\s+/);
    const width = this.offsetWidth;
    const height = this.offsetHeight;

    const start = s ? parseFloat(s) : 0.05;
    const end = e ? parseFloat(e) : 0.35;

    this.#container.innerHTML = `
      <svg xmlns="http://www.w3.org/2000/svg"
        overflow="visible"
        shape-rendering="geometricPrecision"
        preserveAspectRatio="none"
        viewBox="0 0 ${width} ${height}"
      >
        <path vector-effect="non-scaling-stroke" d="
          M${width * start} ${height * start}
          L${width * end} ${height * end}
        " />
        <path vector-effect="non-scaling-stroke" d="
          M${width * (1 - start)} ${height * start}
          L${width * (1 - end)} ${height * end}
        " />
        <path vector-effect="non-scaling-stroke" d="
          M${width * (1 - start)} ${height * (1 - start)}
          L${width * (1 - end)} ${height * (1 - end)}
        " />
        <path vector-effect="non-scaling-stroke" d="
          M${width * start} ${height * (1 - start)}
          L${width * end} ${height * (1 - end)}
        " />
      </svg>
    `;
  };
}

customElements.define('lowrisc-crossbar', LowriscCrossbar);

class LowriscArrow extends LowriscBlock {
  static observedAttributes = [...super.observedAttributes, "horizontal", "head"];

  update() {
    super.update();
    this.classList.add("lowrisc-arrow");

    const horizontal = this.hasAttribute("horizontal");
    const [overhang_ratio = 1, height_ratio = 0.8] = (this.getAttribute("head") || "1 0.6").split(/\s+/);

    const width = horizontal ? this.offsetHeight : this.offsetWidth;
    const length = horizontal ? this.offsetWidth : this.offsetHeight;
    const overhang = width * overhang_ratio / 2;
    const height = width * height_ratio;

    const L = horizontal ? (x, y) => `${y} ${x}` : (x, y) => `${x} ${y}`;

    this.innerHTML = `
      <svg xmlns="http://www.w3.org/2000/svg"
        overflow="visible"
        shape-rendering="geometricPrecision"
        preserveAspectRatio="none"
        viewBox="0 0 ${L(width, length)}"
      >
        <path vector-effect="non-scaling-stroke" d="
          M${L(0, height)}
          l${L(-overhang, 0)}
          l${L(overhang + width / 2, -height)}
          l${L(overhang + width / 2, height)}
          l${L(-overhang, 0)}
          l${L(0, length - 2 * height)}
          l${L(overhang, 0)}
          l${L(-overhang - width / 2, height)}
          l${L(-overhang - width / 2, -height)}
          l${L(overhang, 0)}
          Z
        "
        />
      </svg>
    `;
  };
}

customElements.define('lowrisc-arrow', LowriscArrow);
