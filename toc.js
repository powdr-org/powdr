// Populate the sidebar
//
// This is a script, and not included directly in the page, to control the total size of the book.
// The TOC contains an entry for each page, so if each page includes a copy of the TOC,
// the total size of the page becomes O(n**2).
class MDBookSidebarScrollbox extends HTMLElement {
    constructor() {
        super();
    }
    connectedCallback() {
        this.innerHTML = '<ol class="chapter"><li class="chapter-item expanded affix "><li class="part-title">powdrVM</li><li class="chapter-item expanded "><a href="powdr_vm_intro.html"><strong aria-hidden="true">1.</strong> Introduction</a></li><li class="chapter-item expanded affix "><li class="part-title">Getting Started with powdrVM</li><li class="chapter-item expanded "><a href="installation_vm.html"><strong aria-hidden="true">2.</strong> Installation</a></li><li class="chapter-item expanded "><a href="quick_start_vm.html"><strong aria-hidden="true">3.</strong> Quick Start</a></li><li class="chapter-item expanded affix "><li class="part-title">powdr SDK</li><li class="chapter-item expanded "><a href="powdr_sdk_intro.html"><strong aria-hidden="true">4.</strong> Introduction</a></li><li class="chapter-item expanded affix "><li class="part-title">Getting Started with powdr SDK</li><li class="chapter-item expanded "><a href="installation_sdk.html"><strong aria-hidden="true">5.</strong> Installation</a></li><li class="chapter-item expanded "><a href="hello_world.html"><strong aria-hidden="true">6.</strong> Hello World</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="hello_world_cli.html"><strong aria-hidden="true">6.1.</strong> in the CLI</a></li><li class="chapter-item expanded "><a href="powdr_crate.html"><strong aria-hidden="true">6.2.</strong> as a library</a></li><li class="chapter-item expanded "><a href="hello_world_ethereum.html"><strong aria-hidden="true">6.3.</strong> verified on Ethereum</a></li><li class="chapter-item expanded "><a href="hello_world_ethereum_aggregation.html"><strong aria-hidden="true">6.4.</strong> verified on Ethereum with proof aggregation</a></li></ol></li><li class="chapter-item expanded "><a href="examples.html"><strong aria-hidden="true">7.</strong> Examples</a></li><li class="chapter-item expanded "><a href="publics.html"><strong aria-hidden="true">8.</strong> Using publics</a></li><li class="chapter-item expanded affix "><li class="part-title">powdr SDK Reference Guide</li><li class="chapter-item expanded "><a href="cli/index.html"><strong aria-hidden="true">9.</strong> CLI</a></li><li class="chapter-item expanded "><a href="asm/index.html"><strong aria-hidden="true">10.</strong> asm</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="asm/modules.html"><strong aria-hidden="true">10.1.</strong> Modules</a></li><li class="chapter-item expanded "><a href="asm/declarations.html"><strong aria-hidden="true">10.2.</strong> Declarations</a></li><li class="chapter-item expanded "><a href="asm/machines.html"><strong aria-hidden="true">10.3.</strong> Machines</a></li><li class="chapter-item expanded "><a href="asm/registers.html"><strong aria-hidden="true">10.4.</strong> Registers</a></li><li class="chapter-item expanded "><a href="asm/functions.html"><strong aria-hidden="true">10.5.</strong> Functions</a></li><li class="chapter-item expanded "><a href="asm/expressions.html"><strong aria-hidden="true">10.6.</strong> Expressions</a></li><li class="chapter-item expanded "><a href="asm/instructions.html"><strong aria-hidden="true">10.7.</strong> Instructions</a></li><li class="chapter-item expanded "><a href="asm/operations.html"><strong aria-hidden="true">10.8.</strong> Operations</a></li><li class="chapter-item expanded "><a href="asm/links.html"><strong aria-hidden="true">10.9.</strong> Links</a></li></ol></li><li class="chapter-item expanded "><a href="pil/index.html"><strong aria-hidden="true">11.</strong> pil</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="pil/declarations.html"><strong aria-hidden="true">11.1.</strong> Declarations</a></li><li class="chapter-item expanded "><a href="pil/expressions.html"><strong aria-hidden="true">11.2.</strong> Expressions</a></li><li class="chapter-item expanded "><a href="pil/patterns.html"><strong aria-hidden="true">11.3.</strong> Patterns</a></li><li class="chapter-item expanded "><a href="pil/types.html"><strong aria-hidden="true">11.4.</strong> Types</a></li><li class="chapter-item expanded "><a href="pil/fixed_columns.html"><strong aria-hidden="true">11.5.</strong> Fixed Columns</a></li><li class="chapter-item expanded "><a href="pil/builtins.html"><strong aria-hidden="true">11.6.</strong> Built-in Functions</a></li></ol></li><li class="chapter-item expanded "><a href="frontends/index.html"><strong aria-hidden="true">12.</strong> Frontends</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="frontends/riscv.html"><strong aria-hidden="true">12.1.</strong> RISCV</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="frontends/zk-continuations.html"><strong aria-hidden="true">12.1.1.</strong> zk-Continuations</a></li></ol></li><li class="chapter-item expanded "><a href="frontends/valida.html"><strong aria-hidden="true">12.2.</strong> Valida</a></li><li class="chapter-item expanded "><a href="frontends/evm.html"><strong aria-hidden="true">12.3.</strong> EVM</a></li></ol></li><li class="chapter-item expanded "><a href="backends/index.html"><strong aria-hidden="true">13.</strong> Backends</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="backends/plonky3.html"><strong aria-hidden="true">13.1.</strong> plonky3</a></li><li class="chapter-item expanded "><a href="backends/halo2.html"><strong aria-hidden="true">13.2.</strong> Halo2</a></li><li class="chapter-item expanded "><a href="backends/estark.html"><strong aria-hidden="true">13.3.</strong> eSTARK</a></li></ol></li><li class="chapter-item expanded "><a href="architecture/index.html"><strong aria-hidden="true">14.</strong> Architecture</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="architecture/compiler.html"><strong aria-hidden="true">14.1.</strong> Compiler</a></li><li class="chapter-item expanded "><a href="architecture/linker.html"><strong aria-hidden="true">14.2.</strong> Linker</a></li></ol></li></ol>';
        // Set the current, active page, and reveal it if it's hidden
        let current_page = document.location.href.toString().split("#")[0];
        if (current_page.endsWith("/")) {
            current_page += "index.html";
        }
        var links = Array.prototype.slice.call(this.querySelectorAll("a"));
        var l = links.length;
        for (var i = 0; i < l; ++i) {
            var link = links[i];
            var href = link.getAttribute("href");
            if (href && !href.startsWith("#") && !/^(?:[a-z+]+:)?\/\//.test(href)) {
                link.href = path_to_root + href;
            }
            // The "index" page is supposed to alias the first chapter in the book.
            if (link.href === current_page || (i === 0 && path_to_root === "" && current_page.endsWith("/index.html"))) {
                link.classList.add("active");
                var parent = link.parentElement;
                if (parent && parent.classList.contains("chapter-item")) {
                    parent.classList.add("expanded");
                }
                while (parent) {
                    if (parent.tagName === "LI" && parent.previousElementSibling) {
                        if (parent.previousElementSibling.classList.contains("chapter-item")) {
                            parent.previousElementSibling.classList.add("expanded");
                        }
                    }
                    parent = parent.parentElement;
                }
            }
        }
        // Track and set sidebar scroll position
        this.addEventListener('click', function(e) {
            if (e.target.tagName === 'A') {
                sessionStorage.setItem('sidebar-scroll', this.scrollTop);
            }
        }, { passive: true });
        var sidebarScrollTop = sessionStorage.getItem('sidebar-scroll');
        sessionStorage.removeItem('sidebar-scroll');
        if (sidebarScrollTop) {
            // preserve sidebar scroll position when navigating via links within sidebar
            this.scrollTop = sidebarScrollTop;
        } else {
            // scroll sidebar to current active section when navigating via "next/previous chapter" buttons
            var activeSection = document.querySelector('#sidebar .active');
            if (activeSection) {
                activeSection.scrollIntoView({ block: 'center' });
            }
        }
        // Toggle buttons
        var sidebarAnchorToggles = document.querySelectorAll('#sidebar a.toggle');
        function toggleSection(ev) {
            ev.currentTarget.parentElement.classList.toggle('expanded');
        }
        Array.from(sidebarAnchorToggles).forEach(function (el) {
            el.addEventListener('click', toggleSection);
        });
    }
}
window.customElements.define("mdbook-sidebar-scrollbox", MDBookSidebarScrollbox);
