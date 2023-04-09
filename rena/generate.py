import os
from jinja2 import Environment, FileSystemLoader
from collections import namedtuple
import re

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

Dish = namedtuple('Dish', ['name', 'price', 'descr', 'image', 'thumb'])

dish_data = {}

for category, files in sorted(dish_data_raw.items(), key=lambda x: x[0]):
    dish_data[category] = []

    for file in files:
        # extract the stuff between brackets from the filename using a regex
        cleaned = file.replace(',', ', ').replace(',  ', ', ').replace('( ', '(').replace('(', ' (').replace('  (', ' (')
        name, price = cleaned.rsplit('-', 1)
        name = name.capitalize()
        name,descr = (name.split('(') + [''])[0:2]
        name = name.replace("gedroogde fruit", "gedroogd fruit")
        descr = descr.replace(')', '')
        price = price.replace('€', '')
        price = price.strip().rsplit('.', 1)[0]
        # replace point with comma if preceded by a number
        price = re.sub(r'(\d)\.(\d)', r'\1,\2', price)
        image = f'menu/{category}/{file}'
        thumb = os.path.splitext(image)[0] + "_thumb" + os.path.splitext(image)[1]
        dish_data[category].append(Dish(name.strip(), price, descr, image, thumb))

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