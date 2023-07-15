
    window.addEventListener('hashchange', function() {
        // Check if the hash matches the pattern 'line-xx'
        var match = location.hash.match(/^#line-(\d+)$/);
        if (match) {
            // Remove the existing class from any other line
            var oldElem = document.querySelector(".highlighted");
            if(oldElem){
                oldElem.classList.remove("highlighted");
            }

            // Add the class to the new line
            var id = 'linespan-' + match[1];
            var elem = document.getElementById(id);
            if (elem) {
                elem.classList.add("highlighted");

                // Scroll to the element
                var topPos = elem.offsetTop - window.innerHeight / 4;
                setTimeout(function() { window.scrollTo({ top: topPos, behavior: 'smooth' }); }, 100);
            }
        }
    });

    // Trigger hashchange event on page load in case the URL already contains a hash
    document.addEventListener('DOMContentLoaded', (event) => {
        window.dispatchEvent(new HashChangeEvent('hashchange'));
    });
    