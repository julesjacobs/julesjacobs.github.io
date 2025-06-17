# StacKAT Slides - Claude Code Context

This directory contains the presentation slides for the StacKAT paper.

## Structure

- `slides.html` - Main presentation file using Reveal.js
- `slides.css` - Extracted CSS styles for the presentation
- `slides.js` - JavaScript code for animations and interactions
- `stackatv1.html` - Interactive demo loaded into the slides via an iframe
- `tikz-sources/` - LaTeX/TikZ source files for diagrams
- `tikz-svg/` - Generated SVG files from TikZ sources
- `convert-tikz-to-svg.sh` - Script to convert TikZ to SVG

## Animations

The presentation includes two main packet animations:

1. **Basic Packet Animation** - Shows packet routing through a network with field updates (switch, TTL, VLAN)
2. **StacKAT Packet Animation** - Enhanced version that demonstrates payload transformations using push/pop operations

### Recent Updates

- Fixed payload display to show realistic binary patterns (starting with "101010")
- Implemented push/pop bit operations that modify the payload at each hop
- Right-aligned payload display to make push/pop operations more visible
- Fixed field highlighting to properly scope to each animation
- Refactored CSS and JavaScript into separate files for better maintainability

## Development Notes

- The animations use Reveal.js for presentation framework
- Each animation is self-contained with its own HTML structure and class instances
- Field highlighting is scoped to prevent interference between animations
- Payload transformations randomly push 1-3 bits or pop 1-3 bits from the front