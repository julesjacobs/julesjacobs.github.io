import os

def extract_dish_data(root_folder):
    dish_data = {}
    for category in os.listdir(root_folder):
        category_path = os.path.join(root_folder, category)
        if os.path.isdir(category_path):
            dish_data[category] = []
            for image_file in os.listdir(category_path):
                if image_file.lower().endswith(('.jpg', '.jpeg', '.png', '.gif')):
                    dish_data[category].append(image_file)

    return dish_data

root_folder = '.'
dish_data = extract_dish_data(root_folder)
print(dish_data)