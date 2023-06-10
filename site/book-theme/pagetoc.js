/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

// Original Author
// https://github.com/JorelAli/mdBook-pagetoc

// Un-active everything when you click it
Array.prototype.forEach.call(document.getElementsByClassName("pagetoc")[0].children, function(el) {
    el.addEventHandler("click", function() {
        Array.prototype.forEach.call(document.getElementsByClassName("pagetoc")[0].children, function(el) {
            el.classList.remove("active");
        });
        el.classList.add("active");
    });
});

/* The following functionality highlights the pagetoc entry of the highest visible heading on the page.
 * This gives the pagetoc the dynamic highlighting behaviour as you scroll the page. */
var updateDynamicHighlight = function() {
    var id;
    let elements = document.getElementsByClassName("header");
    // Set id == the highest "header" element visible in the window.
    // Define an offset to account for the menubar, and bump the decision-point a
    // bit further down the page, which makes the behaviour feel more natural.
    const highestVisibleHeaderOffset = 350; // px
    Array.prototype.forEach.call(elements, function(el) {
        if ((window.pageYOffset + highestVisibleHeaderOffset) >= el.offsetTop) {
            id = el;
        }
    });
    if (!id) return;
    // Add the matching <a> pagetoc element to the "active" class (i.e. highlighted).
    // Also scroll the ToC so this element is in-view.
    let pagetoc = document.getElementsByClassName("pagetoc")[0];
    Array.prototype.forEach.call(pagetoc.getElementsByTagName("a"), function(el) {
        if (id.href.localeCompare(el.href) == 0) {
            // Set all <a> elements in the pagetoc inactive.
            Array.prototype.forEach.call(pagetoc.getElementsByTagName("a"), function(el) {
                el.classList.remove("active");
            });
            // Set the matched <a> element as 'active'
            el.classList.add("active");

            // Scroll "active" element into view (the middle of the scrollable pagetoc hopefully)
            document.getElementsByClassName("pagetoc")[0]
                .scrollTo({ top: el.offsetTop - (pagetoc.getBoundingClientRect().height / 2 ) ,
                            behavior: 'smooth' });
        }
    });
};
window.addEventListener("load", updateDynamicHighlight);
window.addEventListener("scroll", updateDynamicHighlight);

/* Style the heading that matches the URL fragment (i.e. when you click a hyperlink).
 * - Find the element with the ":target" psuedoclass applied
 * - Measure it's rendered height, and set the '--target-height' variable to this value.
 * - The CSS selected by ":target" will style the horizontal highlighting bar to match this height. */
var set_target_highlight = function(event) {
    let newurl = '';
    if (typeof(event.newURL) === 'undefined') {
        // probably a "load" event
        newurl = window.location.href;
    } else {
        // "hashchange" event
        newurl = event.newURL;
    }
    // Along with "margin-top: -10px;" applied to the :target selector style, this gives the
    // highlight a top and bottom margin of 10px around the heading.
    const targetMarginTopBottom = 20; // px
    Array.prototype.forEach.call(document.getElementsByClassName("header"), function(el) {
        if (new URL(el.href).hash == new URL(newurl).hash) {
            document.documentElement.style.setProperty(
                '--target-height', (el.getBoundingClientRect().height + targetMarginTopBottom) + "px"
            );
            // scroll-margin-top does not seem to work for the first header on a page, so manually
            // force into view if we nav to it.
            if (el === document.getElementsByClassName("header")[0]) { el.scrollIntoView(false); }
        }
    });
};
window.addEventListener("hashchange", set_target_highlight);
window.addEventListener("load", set_target_highlight);

/* Set the "height" style of pagetoc conditionally.
 * - auto    -> for short lists that don't overflow, limit the height of the pagetoc, disables scrollbar.
 * - limited -> content overflows the element, and therefore scrolling is enabled */
var set_pagetoc_height = function() {
    let el = document.getElementsByClassName("pagetoc")[0];
    el.style.height = "auto";
    // Add some extra margin-bottom to the pagetoc, to keep away from the bottom of the page.
    const pagetocMarginBottom = 200; // px
    let pagetoc_height = el.getBoundingClientRect().height + pagetocMarginBottom;
    let window_height = window.innerHeight - document.documentElement.style.getPropertyValue('--menu-bar-height');
    if (pagetoc_height < window_height) {
        el.style.height = "auto";
    } else {
        el.style.height = "calc(90vh - var(--menu-bar-height))"; // limited_height
    }
};
window.addEventListener("resize", set_pagetoc_height);

/* create_pagetoc_structure()
 * Dynamically create a tree of <a> elements for each heading in
 * the content body, with wrapper divs for each level of heirarchy.
 * This will allow formatting/styling which better illustrates the
 * structure of the page.
 * Add the created structure within the 'pagetoc' element.
 *
 *    //  /-> headerElements[idx] // In-order array of section headings down the page
 *    //  |
 *    //  |
 *    //    // ----
 *    //  0 // H1 |
 *    //  1 // H1 |
 *    //  2 // H1 |
 *    //  - // W1---------
 *    //  3 // |      H2 |
 *    //  4 // |      H2 |
 *    //  - // |      W2---------
 *    //  5 // |      |      H3 |
 *    //  6 // |      |      H3 |
 *    //    // |      -----------
 *    //  7 // |      H2 |
 *    //  - // |      W2---------
 *    //  8 // |      |      H3 |
 *    //    // ------------------
 *    //  9 // H1 |
 *    // 10 // H1 |
 *    // -  // W1---------
 *    // 11 // |      H2 |
 *    // 12 // |      H2 |
 *    // -  // |      W2---------
 *    // 13 // |      |      H3 |
 *    // 14 // |      |      H3 |
 *    //    // |      -----------
 *    // 15 // |      H2 |
 *    // -  // |      W2---------
 *    // 16 // |      |      H3 |
 *    //    // ------------------
 *    // 17 // H1 |
 *    //    // ----
 *
 *    LeafNode -> createAnchorElement(idx)
 */

var create_pagetoc_structure = function(el_pagetoc) {
    // Search the page for all <H*> elements
    let headerElements = Array.from(document.getElementsByClassName("header"));
    // Don't show the pagetoc if there are not enough heading elements.
    if (headerElements.length <= 1) {
        document.getElementsByClassName("sidetoc")[0].classList.add("hidden");
        return;
    }
    // Filter-out heading elements we don't want to show.
    // The default list hides some headings used within the register map, which
    // greatly reduces noise and keeps the list a manageable length.
    // TODO add configurable filter, or design a standard id across the project docs.
    //      e.g in-page metadata could be picked up to specify an exclude list.
    const id_keywords = ['field', 'fields', "instances"];
    headerElements = headerElements.filter(h =>
        (id_keywords.filter(i => h.parentElement.id.includes(i))).length === 0
    );

    // Add title div to ToC
    let title = document.createElement("div");
    title.appendChild(document.createTextNode("Table of Contents"));
    title.setAttribute("id", "pagetoc-title");
    el_pagetoc.appendChild(title);

    //////////////////////////////////
    // Define some helper functions //
    //////////////////////////////////

    // Create an <a> element for a clickable link
    function createAnchorElement(idx) {
        let el = headerElements[idx];
        // Some headings may have different structures, or may be malformed.
        // Deal with this, somewhat gracefully. At least try not to crash.
        try {
            let link = document.createElement("a");
            // A heading which is also a link is generated with a slightly different structure
            // The heading text is in an adjacent <a> tag, but we use the href from the first <a> elem.
            let el_with_text;
            if (el.text.length === 0) {
                el_with_text = el.nextElementSibling;
            } else {
                el_with_text = el;
            }
            link.appendChild(document.createTextNode(el_with_text.text));
            link.href = el.href;
            link.classList.add("leaf-" + el.parentElement.tagName);
            return link;
        }
        catch(err) {
            console.log(err);
            return document.createElement("a");
        }
    }
    function getHnum(idx) {
        return parseInt(headerElements[idx].parentElement.nodeName[1]);
    }
    // Return idx of the next element with a larger Hnum.
    function getNextHigherH (idxCur) {
        let hCur = getHnum(idxCur);
        for (let i = idxCur + 1; i < headerElements.length; i++) {
            if (hCur > getHnum(i)) {return i;}
        }
        return headerElements.length;
    }
    // Create a wrapper element encompassing headings from
    // startIdx to stopIdx, recursively adding more wrappers if
    // headings in the range are lower Hnum.
    // Strictly, 'startIdx <= stopIdx'
    // This allows the heirarchy of the headings to be mirrored
    // within the pagetoc structure, allowing for some context-aware
    // formatting options.
    function wrapAllDescendingElems(
        wLevel, // wrapperLevel (the H* index)
        startIdx, stopIdx)
    {
        console.assert(startIdx <= stopIdx, "Strictly, 'stopIdx <= startIdx' is required.");
        let wrap = document.createElement("div");
        wrap.classList.add(`wrap-W${wLevel}`);

        // Loop over the range given, descending recursively where needed.
        let i = startIdx;
        while (i <= stopIdx) {
            let h = getHnum(i);

            if (h === wLevel) {
                wrap.appendChild(createAnchorElement(i));
                i++;
            } else if (h > wLevel) {
                wrap.appendChild(wrapAllDescendingElems(h, // wrapperLevel
                    i, getNextHigherH(i) - 1 // startIdx, stopIdx
                ));
                i = getNextHigherH(i);
            } else if (h < wLevel) { console.log(`Break_H_LessThan_W(${i})`); break; }
        }
        return wrap;
    }

    // Invoke the above helper-functions to create the tree
    let tree = wrapAllDescendingElems(0, 0, headerElements.length - 1);
    el_pagetoc.appendChild(tree);
};



/* Populate the pagetoc sidebar on load
 * - Create a tree structure of elements within the pagetoc nav item
 * - Update the overflow height behaviour when the rendered size is known. */
window.addEventListener('load', function() {
    let pagetoc = document.getElementsByClassName("pagetoc")[0];
    create_pagetoc_structure(pagetoc);

    setTimeout(function(){
        // Allow the pagetoc to complete drawing, so we can measure it's final height.
        // TODO find a better way to do this.
        set_pagetoc_height.call();
    }, 1000);
});
