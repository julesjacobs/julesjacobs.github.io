# Repository Structure Analysis

This document provides an overview of the repository structure, identifying the purpose of files and directories and highlighting potential cleanup opportunities.

## Core Website Structure (Jekyll-based)

| Path | Purpose | Cleanup Status |
| ---- | ------- | -------------- |
| `_config.yml` | Jekyll configuration file | Active, keep |
| `_posts/` | Blog posts (2014-2024) | Active, keep |
| `_drafts/` | Draft posts | Active, keep |
| `_includes/` | Jekyll template components | Active, keep |
| `_layouts/` | Jekyll page layouts | Active, keep |
| `_sass/` | SCSS styling files | Active, keep |
| `css/` | Main CSS files | Active, keep |
| `Gemfile`, `Gemfile.lock` | Ruby dependencies | Active, keep |
| `CNAME` | GitHub Pages domain config | Active, keep |
| `feed.xml` | RSS feed configuration | Active, keep |
| `index.html` | Main page | Active, keep |
| `about.md` | About page | Active, keep |
| `blog.html` | Blog listing page | Active, keep |
| `research.html` | Research page | New, keep |
| `newpost.py` | Script for creating new posts | Active, keep |

## Academic Content

| Path | Purpose | Cleanup Status |
| ---- | ------- | -------------- |
| `notes/` | Mathematical and CS technical notes | Active, but contains build artifacts |
| `papers/` | Academic papers with supporting materials | Active, keep |
| `slides/` | Presentation slides (2020-2024) | Active, keep |
| `pdf/` | Research papers | Active, but has some duplicates |
| `code/` | Code examples for blog posts | Active but sparse, could reorganize |

## Media Content

| Path | Purpose | Cleanup Status |
| ---- | ------- | -------------- |
| `photos/` | Personal photography collection | Active, but contains duplicate thumbnails |
| `photos/thumbnails/` | Generated thumbnails | Could be regenerated, consider gitignoring |
| `images/` | Site images and icons | Active, keep |
| `favicon.ico` | Site favicon | Active, keep |

## Other Directories

| Path | Purpose | Cleanup Status |
| ---- | ------- | -------------- |
| `adhoc/` | Miscellaneous files | Low use, consider reorganizing |
| `lyx/` | LyX document files | Contains temporary backup files |
| `misc/` | Miscellaneous content | Various standalone projects |
| `yt/` | YouTube related content | Single file, possibly obsolete |
| `downloads/` | Downloadable content | Sparse, keep but review |

## Cleanup Recommendations

### Files to Delete

1. **LaTeX build artifacts**:
   - `*.aux`, `*.fdb_latexmk`, `*.fls`, `*.log`, `*.synctex.gz`, `*.blg`, `*.bbl`
   - Primarily in `notes/` and subdirectories
   - These are temporary compilation files that should not be versioned

2. **LyX backup files**:
   - `*.lyx~` files and `#*.lyx#` temporary files in the `lyx/` directory
   - These are editor backup files and should be gitignored

3. **Build directories**:
   - All `target/` directories in `notes/nfa/`, `notes/satpre/`, `notes/smartconstr/`
   - These contain compiled code and build artifacts that should be regenerated

### Content to Reorganize

1. **Duplicate PDFs**:
   - Some PDFs appear in both `notes/` subdirectories and the `pdf/` directory
   - Example: `sympoly.pdf` exists in multiple locations
   - Consider consolidating to a single location

2. **Nested duplicates**:
   - Directories like `notes/smartconstr/smartconstr/` contain duplicate hierarchies
   - Consider flattening or reorganizing these structures

3. **Photo thumbnails**:
   - `photos/thumbnails/` contains duplicates of images from the parent directory
   - Consider generating these at build time instead of storing in git

### `.gitignore` Updates

Consider updating the `.gitignore` file to exclude:
- All LaTeX build artifacts (`*.aux`, `*.log`, etc.)
- LyX backup files (`*.lyx~`, `#*#`)
- Build directories (`target/`, `_site/`, etc.)
- Generated thumbnails if they're kept