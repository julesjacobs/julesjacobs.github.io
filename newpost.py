#!/usr/bin/env python3

import sys
import os
from datetime import datetime
import re

def create_post(title):
    # Get the current date
    date_str = datetime.now().strftime("%Y-%m-%d")
    
    # Create the filename
    filename = f"{date_str}-{re.sub('[^a-zA-Z0-9-]', '', title.lower().replace(' ', '-'))}.md"
    filepath = os.path.join("_posts", filename)
    
    # Create the content
    content = f"""---
title: "{title}"
---

"""
    
    # Write the content to the file
    with open(filepath, 'w') as file:
        file.write(content)
    
    print(f"New post created: {filepath}")

if __name__ == "__main__":
    title = input("Enter the title of the post: ")
    create_post(title)
