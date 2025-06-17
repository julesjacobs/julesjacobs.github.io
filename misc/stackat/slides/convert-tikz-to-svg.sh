#!/bin/bash

# Script to convert TikZ files to SVG for use in HTML slides

# Colors for output
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# Directories
SOURCE_DIR="tikz-sources"
OUTPUT_DIR="tikz-svg"

# Create output directory
mkdir -p "$OUTPUT_DIR"

echo -e "${GREEN}Converting TikZ files to SVG...${NC}"

# Check if source directory exists
if [ ! -d "$SOURCE_DIR" ]; then
    echo -e "${RED}Error: TikZ source directory '$SOURCE_DIR' not found${NC}"
    exit 1
fi

# Process all .tex files in the source directory
for tex_file in "$SOURCE_DIR"/*.tex; do
    if [ -f "$tex_file" ]; then
        base_name=$(basename "$tex_file" .tex)
        echo -e "${YELLOW}Processing $base_name.tex...${NC}"
        
        # Copy file temporarily to current directory for compilation
        cp "$tex_file" "$base_name.tex"
        
        # Compile to PDF
        pdflatex -interaction=nonstopmode "$base_name.tex" > /dev/null 2>&1
        
        if [ -f "$base_name.pdf" ]; then
            # Convert PDF to SVG
            if command -v pdf2svg &> /dev/null; then
                pdf2svg "$base_name.pdf" "$OUTPUT_DIR/$base_name.svg"
                echo -e "${GREEN}✓ Created $OUTPUT_DIR/$base_name.svg${NC}"
            elif command -v inkscape &> /dev/null; then
                inkscape "$base_name.pdf" --export-plain-svg="$OUTPUT_DIR/$base_name.svg" 2>/dev/null
                echo -e "${GREEN}✓ Created $OUTPUT_DIR/$base_name.svg (via Inkscape)${NC}"
            else
                echo -e "${RED}✗ No PDF to SVG converter found for $base_name${NC}"
            fi
            
            # Clean up temporary files
            rm -f "$base_name.tex" "$base_name.pdf" "$base_name.aux" "$base_name.log"
        else
            echo -e "${RED}✗ Failed to compile $base_name.tex${NC}"
            # Clean up temporary tex file
            rm -f "$base_name.tex"
        fi
    fi
done

# Create an index HTML file to preview all figures
cat > "$OUTPUT_DIR/preview.html" << 'EOF'
<!DOCTYPE html>
<html>
<head>
    <title>TikZ Figures for StacKAT Slides</title>
    <style>
        body {
            font-family: Arial, sans-serif;
            max-width: 1400px;
            margin: 0 auto;
            padding: 20px;
            background-color: #f5f5f5;
        }
        h1 {
            color: #333;
            text-align: center;
        }
        .figure-grid {
            display: grid;
            grid-template-columns: repeat(auto-fill, minmax(450px, 1fr));
            gap: 30px;
            margin-top: 30px;
        }
        .figure-box {
            background: white;
            border: 1px solid #ddd;
            border-radius: 8px;
            padding: 20px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }
        .figure-box h3 {
            margin-top: 0;
            color: #555;
            font-size: 1.1em;
            word-break: break-word;
        }
        .figure-box img {
            width: 100%;
            height: auto;
            background: white;
            padding: 10px;
            border: 1px solid #eee;
            border-radius: 4px;
        }
        .download-link {
            display: inline-block;
            margin-top: 10px;
            padding: 5px 10px;
            background: #007bff;
            color: white;
            text-decoration: none;
            border-radius: 4px;
            font-size: 0.9em;
        }
        .download-link:hover {
            background: #0056b3;
        }
        .code-snippet {
            background: #f8f8f8;
            border: 1px solid #e0e0e0;
            border-radius: 4px;
            padding: 10px;
            margin-top: 10px;
            font-family: monospace;
            font-size: 0.85em;
            overflow-x: auto;
        }
    </style>
</head>
<body>
    <h1>TikZ Figures for StacKAT Slides</h1>
    <p style="text-align: center; color: #666;">These SVG figures can be embedded directly in the presentation slides.</p>
    <div class="figure-grid">
EOF

# Add each SVG to the preview
for svg_file in "$OUTPUT_DIR"/*.svg; do
    if [ -f "$svg_file" ]; then
        base_name=$(basename "$svg_file" .svg)
        cat >> "$OUTPUT_DIR/preview.html" << EOF
        <div class="figure-box">
            <h3>$base_name</h3>
            <img src="$(basename "$svg_file")" alt="$base_name">
            <div class="code-snippet">
                &lt;img src="tikz-svg/$base_name.svg" style="max-width: 100%;"&gt;
            </div>
            <a href="$(basename "$svg_file")" download class="download-link">Download SVG</a>
        </div>
EOF
    fi
done

cat >> "$OUTPUT_DIR/preview.html" << 'EOF'
    </div>
    
    <div style="margin-top: 40px; padding: 20px; background: #e8f4f8; border-radius: 8px;">
        <h2 style="color: #333;">How to use these figures in slides:</h2>
        <ol>
            <li>Copy the code snippet from each figure box</li>
            <li>Paste it into your HTML slides where you want the figure to appear</li>
            <li>Adjust the styling as needed (e.g., width, alignment)</li>
        </ol>
        <p>Example with custom styling:</p>
        <div class="code-snippet">
            &lt;div style="text-align: center; margin: 20px 0;"&gt;<br>
            &nbsp;&nbsp;&lt;img src="tikz-svg/push-pop-closure-rules.svg" style="width: 80%; max-width: 600px;"&gt;<br>
            &lt;/div&gt;
        </div>
    </div>
</body>
</html>
EOF

echo -e "${GREEN}Done! SVG files are in $OUTPUT_DIR/${NC}"
echo -e "${GREEN}Open $OUTPUT_DIR/preview.html to see all figures${NC}"

# List the generated files
echo -e "\n${GREEN}Generated SVG files:${NC}"
ls -1 "$OUTPUT_DIR"/*.svg 2>/dev/null | sed 's/^/  - /'

# Check if we need to install dependencies
if ! command -v pdf2svg &> /dev/null && ! command -v inkscape &> /dev/null; then
    echo -e "\n${YELLOW}To convert PDFs to SVG, install one of:${NC}"
    echo "  - pdf2svg: brew install pdf2svg"
    echo "  - inkscape: brew install --cask inkscape"
fi