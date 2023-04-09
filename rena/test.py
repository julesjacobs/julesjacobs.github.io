import re

text = "Vinaigrette salade (gekookte groenten, verse kruiden, olijfolie) - 4.99 p.p.jpg"
text = "Luxe salade - 4.80 p.p.jpg"

name = re.findall(r'^\w+\s\w+', text)[0]
description = "".join(re.findall(r'\((.*?)\)', text))
price = re.findall(r'[-+]?\d*\.\d+\s\w+\.\w+', text)[0]

print("Name:", name)
print("Description:", description)
print("Price:", price)