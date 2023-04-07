from PIL import Image

def combine_images_horizontally(images):
    image_objects = [Image.open(img_path) for img_path in images]
    widths, heights = zip(*(i.size for i in image_objects))

    total_width = sum(widths)
    max_height = max(heights)

    new_image = Image.new("RGBA", (total_width, max_height))

    x_offset = 0
    for img in image_objects:
        new_image.paste(img, (x_offset, 0))
        x_offset += img.size[0]

    return new_image

images = ["images/image1.png", "images/image2.png", "images/image3.png", "images/image4.png", "images/image5.png"]
combined_image = combine_images_horizontally(images)
combined_image.save("images/header-background.png")
