import os
from jinja2 import Environment, FileSystemLoader
from collections import namedtuple

def extract_dish_data(root_folder):
    dish_data = {}
    for category in os.listdir(root_folder):
        category_path = os.path.join(root_folder, category)
        if os.path.isdir(category_path):
            dish_data[category] = []
            for image_file in os.listdir(category_path):
                if image_file.lower().endswith(('.jpg', '.jpeg', '.png', '.gif')) and not 'thumb' in image_file:
                    dish_data[category].append(image_file)

    return dish_data

root_folder = 'menu'
dish_data_raw = extract_dish_data(root_folder)

print(dish_data_raw)

Dish = namedtuple('Dish', ['name', 'price', 'image', 'thumb'])

dish_data = {}

for category, files in sorted(dish_data_raw.items(), key=lambda x: x[0]):
    dish_data[category] = []

    for file in files:
        name, price = file.rsplit('-', 1)
        price = price.replace('€', '')
        price = price.strip().rsplit('.', 1)[0]
        image = f'menu/{category}/{file}'
        thumb = os.path.splitext(image)[0] + "_thumb" + os.path.splitext(image)[1]
        dish_data[category].append(Dish(name.strip(), price, image, thumb))

print(dish_data)

import time

last_modified = 0

templatefile = 'template.html'

while True:
    current_modified = os.path.getmtime(templatefile)
    print(current_modified, last_modified)
    if current_modified == last_modified:
        time.sleep(1)
        continue

    env = Environment(loader=FileSystemLoader('.'))
    template = env.get_template(templatefile)
    output = template.render(dish_data=dish_data)

    with open('index.html', 'w') as f:
        f.write(output)

    last_modified = current_modified
    print("index.html generated successfully")