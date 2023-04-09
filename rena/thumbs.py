import os
from PIL import Image, ImageOps

def create_thumbnail(image_path, thumbnail_width=300, thumbnail_height=200, exact=True):
    img = Image.open(image_path)
    img = ImageOps.exif_transpose(img)

    if exact:
        # Crop image to desired aspect ratio
        aspect_ratio = thumbnail_width / thumbnail_height
        img_width, img_height = img.size
        img_aspect_ratio = img_width / img_height
        if img_aspect_ratio <= aspect_ratio:
            new_width = img_width
            new_height = int(new_width / aspect_ratio)
        else:
            new_height = img_height
            new_width = int(new_height * aspect_ratio)

        left = (img_width - new_width) // 2
        top = (img_height - new_height) // 2
        right = left + new_width
        bottom = top + new_height
        img = img.crop((left, top, right, bottom))

        # Resize the image to the desired thumbnail size
        img.thumbnail((thumbnail_width, thumbnail_height))
    else:
        img.thumbnail((thumbnail_width, thumbnail_height))

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
