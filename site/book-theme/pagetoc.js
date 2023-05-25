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
    Array.prototype.forEach.call(elements, function(el) {
        if ((window.pageYOffset + 150) >= el.offsetTop) {
            id = el;
        }
    });
    if (!id) return;
    // Add the matching <a> pagetoc element to the "active" class (i.e. highlighted).
    let pagetoc = document.getElementsByClassName("pagetoc")[0];
    Array.prototype.forEach.call(pagetoc.getElementsByTagName("a"), function(el) {
        if (id.href.localeCompare(el.href) == 0) {
            // Set all <a> elements in the pagetoc inactive.
            Array.prototype.forEach.call(pagetoc.getElementsByTagName("a"), function(el) {
                el.classList.remove("active");
            });
            // Set the matched <a> element as 'active'
            el.classList.add("active");
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
    Array.prototype.forEach.call(document.getElementsByClassName("header"), function(el) {
        if (new URL(el.href).hash == new URL(newurl).hash) {
            document.documentElement.style.setProperty(
                '--target-height',
                el.getBoundingClientRect().height + 20 + "px"
            );
        }
    });
};
window.addEventListener("hashchange", set_target_highlight);
window.addEventListener("load", set_target_highlight);

/* create_pagetoc_structure()
 * Dynamically create a tree of <a> elements for each heading in
 * the content body.
 * Add the created structure within the 'pagetoc' element. */
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

    Array.prototype.forEach.call(headerElements, function (el) {
        var link = document.createElement("a");
        link.appendChild(document.createTextNode(el.text));
        link.href = el.href;
        link.classList.add("pagetoc-" + el.parentElement.tagName);
        el_pagetoc.appendChild(link);
      });
};



/* Populate the pagetoc sidebar on load
 * - Create a tree structure of elements within the pagetoc nav item
 * - Update the overflow height behaviour when the rendered size is known. */
window.addEventListener('load', function() {
    let pagetoc = document.getElementsByClassName("pagetoc")[0];
    create_pagetoc_structure(pagetoc);
});
