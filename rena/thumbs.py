import os
from PIL import Image, ImageOps

def create_thumbnail(image_path, thumbnail_height=200):
    img = Image.open(image_path)
    img = ImageOps.exif_transpose(img)
    # img_ratio = float(img.width) / float(img.height)
    # thumbnail_width = int(thumbnail_height * img_ratio)
    # resize but keep original orientation
    img.thumbnail((500, thumbnail_height))
    thumbnail_path = os.path.splitext(image_path)[0] + "_thumb" + os.path.splitext(image_path)[1]
    img.save(thumbnail_path)

def process_directory(directory):
    for root, dirs, files in os.walk(directory):
        for file in files:
            if file.lower().endswith((".jpg", ".jpeg", ".png", ".bmp", ".gif")) and not "thumb" in file:
                image_path = os.path.join(root, file)
                create_thumbnail(image_path)

create_thumbnail("images/header-background.png", 400)

if __name__ == "__main__":
    input_directory = "menu"
    process_directory(input_directory)
