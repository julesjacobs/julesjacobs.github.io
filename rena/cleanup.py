original_data = {
     'Tapas ( vanaf 2 pers)': ['Humus - 4.50.jpg', 'Tzatziki - 3.50.jpg', 'Yoghurttapas - 3.99 (yoghurt,kaas,dille,knoflook,kruiden).jpg', 'Rode bieten tapas - 3.99.jpg', 'Wortel tapas - 3.99.jpg'],
     'soepen (vanaf 5 pers)': ['Kufte(soep met erwten en gehaktbal)-4.50.jpg', 'Yoghurtsoep - 2.99 p.p.jpg', 'Tomatensoep met balletjes-3.90.jpg', 'Kippensoep-3.99.jpg', 'Linzensoep - 2.99 p.p.jpg', 'courgette soep-2.99.jpg'],
     'Verse broodjes': ['Broodje kaas - 3.80.jpg', 'Broodje kip of cervelaat - 3.99 (2).jpg'],
     'salades (vanaf 3 pers)': ['Pasta salade - 4.50.jpg', 'Ceasar salade - 6.99.jpg', 'Verse salade - 2,99.jpg', 'Komkommer salade met verse dille en zilveruitjes - 3.80.jpg', 'Kipcocktail salade - 5.50.jpg', 'Aardappel salade - 3.99.jpg', 'Rucola salade - 3.90.jpg', 'Rena speciale salade (gekookte groenten,verse kruiden,met of zonder kip,mayo) - 4.99.jpg', 'Nicoise(tonijn) salade- 6.99.jpg', 'Rodekool salade - 3.80.jpg', 'Luxe salade - 4.80.jpg', 'Rena luxe salade (gekookte groenten,walnoten,granaatappel,mayo) - 5.50.jpg', 'Vinaigrette salade (gekookte groenten, verse kruiden, olijfolie) - 4.99.jpg'],
     'Toetjes': ['slagroomtaart - 27.95 (voor 10 pers).jpg', 'Vla met stukjes fruit - 2.80.jpg', 'Chocoladetaart - 29.99 (voor 10 pers).jpg', 'Walnoottaart - 29.99 (voor 10 pers).jpg', 'Stukken cake - 3.00 p.st ( vanaf 8 st).jpg', 'Tiramisu - 3.90.jpg', 'Honingtaart - 32.99 (voor 10 pers).jpg', 'Fruittaart - 29.99 (voor 10 pers).jpg'],
     'Hapjes schotel (vanaf 3 pers)': ['Schotel met diverse soorten kaas en vleeswaren - 9.99.png', 'Hapjes schotel 2 - 9.00 (aubergine rolletjes,sigara borek,gevulde tomaatjes, mini wraps,gevulde paprika,tzatziki).jpg', 'Schotel met diverse soorten kaas-9.00.jpg', 'Schotel met diverse vleeswaren -9.00.jpg', 'Romano tomaat met mozzarella - 3.99.jpg', 'Hapjes schotel 1 - 8.50 (mini wraps,gevulde eieren,mini sandwich,hapjes op brood,gevulde komkommer,olijven).jpg'],
     'Hapjes': ['Fruit op spiesjes - 2.50 p.sp ( vanaf 5 sp).jpg', 'Hapjes op broodjes - 1.90 p.st (vanaf 5 st).jpg', 'Omelet rolletjes - 1.99 p.st (vanaf 5st).jpg', 'Fruitcocktail - 2.59 p.p (vanaf 3 pers).jpg', 'Aubergine rolletjes - 1.99 p.st (vanaf 5st).jpg', 'Balletjes-1.40.jpg', 'Borek met kip of rund gehakt  - 1.99 p.st (vanaf 10st).jpg', 'Gevulde komkommer - 1.10 p.st (vanaf 5st).jpg', 'Sigara borek - 1.80 p.st(vanaf 5st).jpg', 'Gevulde paprika - 1.10 p.st (vanaf 4st).jpg', 'Gevulde tomaatjes - 1.10 p.st (vanaf 4st).jpg', 'Borek met spinazie - 1.90 p.st ( vanaf 10st).jpg', 'Tomaat en mozzarella - 2,50.jpg', 'Mini wraps met kipfilet of kaas - 1.10 p.st (vanaf 5st).jpg', 'Gevulde eieren - 1.10 p.st (vanaf 4 st).jpg', 'Hapjes op prikkers - 1.59 p.st (vanaf 5 st).jpg', 'Blinschik (gevulde pancake met zoetekaas of gehakt) -2.50 p.st (vanaf 5st).jpg'],
     'Hoofdgerechten': ['Rijst met rundvlees en gedroogde fruit - 10,99.jpg', 'Gegrilde kipfilet - 5.80.jpg', 'Sperziebonen roerbak - 5,99.jpg', 'Chicken wings - 1.50 p.st (vanaf 10st).jpg', 'Gevulde wijnbladeren met gehakt of vegetarisch - 1.99 p.st (vanaf 15st).jpg', 'Lasagne originale of vegetarisch -6.99 (vanaf 4 pers).jpg', 'Lule kebab (spiezen van rund of kipgehakt) met aardappelpartjes of rijst - 14.99 (vanaf 3pers).jpg', 'Gehaktkoteletten (rundgehakt of kipgehakt) - 3.50 p. st..jpg', 'Gevulde koolrolletjes met gehakt of vegetarisch - 1.99 p.st (vanaf 15st).jpg', 'Lamskotelet met rijst of aardappelpartjes - 13.80 p.p (vanaf 3pers).jpg', 'Balletjes in tomatensaus - 5.99 p.p (vanaf 3 pers).jpg', 'Gegrilde groenten (champignons,aubergine,courgette, paprika) - 6.50 (vanaf 3pers).jpg', 'Rijstschotel met gedroogde fruit - 6.50 p.p (vanaf 3 pers) (2).jpg', 'Drumsticks - 1,99 p.st ( vanaf 8 st).jpg', 'Beyti kebab (gevuld bladerdeeg met gehakt) - 15.99 p.p (vanaf 3 pers).jpg', 'Rijst - 2.90 p.p.jpg', 'Groenten met balletjes in tomatensaus - 9.50 (vanaf 3pers).jpg', 'Aardappelpartjes - 2.80.jpg', 'Gevulde hele kip met walnoten, ui en kruiden - 23.95.jpg', 'Rijst met kip - 10.95 p.p ( vanaf 3 pers).jpg', 'Rijst met groenten - 6,50.jpg']
}

cleaned_data = {
    "01-Tapas (vanaf 2 pers)": [
        "Humus - €4.50.jpg",
        "Tzatziki - €3.50.jpg",
        "Yoghurt Tapas - €3.99 (yoghurt, kaas, dille, knoflook, kruiden).jpg",
        "Rode Bieten Tapas - €3.99.jpg",
        "Wortel Tapas - €3.99.jpg"
    ],
    "02-Soepen (vanaf 5 pers)": [
        "Kufte (soep met erwten en gehaktbal) - €4.50.jpg",
        "Yoghurtsoep - €2.99 p.p.jpg",
        "Tomatensoep met Balletjes - €3.90.jpg",
        "Kippensoep - €3.99.jpg",
        "Linzensoep - €2.99 p.p.jpg",
        "Courgette Soep - €2.99.jpg"
    ],
    "07-Verse Broodjes": [
        "Broodje Kaas - €3.80.jpg",
        "Broodje Kip of Cervelaat - €3.99.jpg"
    ],
    "03-Salades (vanaf 3 pers)": [
        "Pasta Salade - €4.50.jpg",
        "Ceasar Salade - €6.99.jpg",
        "Verse Salade - €2.99.jpg",
        "Komkommer Salade met Verse Dille en Zilveruitjes - €3.80.jpg",
        "Kipcocktail Salade - €5.50.jpg",
        "Aardappel Salade - €3.99.jpg",
        "Rucola Salade - €3.90.jpg",
        "Rena Speciale Salade (gekookte groenten, verse kruiden, met of zonder kip, mayo) - €4.99.jpg",
        "Nicoise (tonijn) Salade - €6.99.jpg",
        "Rodekool Salade - €3.80.jpg",
        "Luxe Salade - €4.80.jpg",
        "Rena Luxe Salade (gekookte groenten, walnoten, granaatappel, mayo) - €5.50.jpg",
        "Vinaigrette Salade (gekookte groenten, verse kruiden, olijfolie) - €4.99.jpg"
    ],
    "08-Toetjes": [
        "Slagroomtaart - €27.95 (voor 10 pers).jpg",
        "Vla met Stukjes Fruit - €2.80.jpg",
        "Chocoladetaart - €29.99 (voor 10 pers).jpg",
        "Walnoottaart - €29.99 (voor 10 pers).jpg",
        "Stukken Cake - €3.00 p.st (vanaf 8 st).jpg",
        "Tiramisu - €3.90.jpg",
        "Honingtaart - €32.99 (voor 10 pers).jpg",
        "Fruittaart - €29.99 (voor 10 pers).jpg"
    ],
    "06-Hapjes Schotel (vanaf 3 pers)": [
        "Schotel met Diverse Soorten Kaas en Vleeswaren - €9.99.png",
        "Hapjes Schotel 2 - €9.00 (aubergine rolletjes, sigara borek, gevulde tomaatjes, mini wraps, gevulde paprika, tzatziki).jpg",
        "Schotel met Diverse Soorten Kaas - €9.00.jpg",
        "Schotel met Diverse Vleeswaren - €9.00.jpg",
        "Romano Tomaat met Mozzarella - €3.99.jpg",
        "Hapjes Schotel 1 - €8.50 (mini wraps, gevulde eieren, mini sandwich, hapjes op brood, gevulde komkommer, olijven).jpg"
    ],
    "05-Hapjes": [
        "Fruit op Spiesjes - €2.50 p.st (vanaf 5 st).jpg",
        "Hapjes op Broodjes - €1.90 p.st (vanaf 5 st).jpg",
        "Omelet Rolletjes - €1.99 p.st (vanaf 5 st).jpg",
        "Fruitcocktail - €2.59 p.p (vanaf 3 pers).jpg",
        "Aubergine Rolletjes - €1.99 p.st (vanaf 5 st).jpg",
        "Balletjes - €1.40.jpg",
        "Borek met Kip of Rund Gehakt - €1.99 p.st (vanaf 10 st).jpg",
        "Gevulde Komkommer - €1.10 p.st (vanaf 5 st).jpg",
        "Sigara Borek - €1.80 p.st (vanaf 5 st).jpg",
        "Gevulde Paprika - €1.10 p.st (vanaf 4 st).jpg",
        "Gevulde Tomaatjes - €1.10 p.st (vanaf 4 st).jpg",
        "Borek met Spinazie - €1.90 p.st (vanaf 10 st).jpg",
        "Tomaat en Mozzarella - €2.50.jpg",
        "Mini Wraps met Kipfilet of Kaas - €1.10 p.st (vanaf 5 st).jpg",
        "Gevulde Eieren - €1.10 p.st (vanaf 4 st).jpg",
        "Hapjes op Prikkers - €1.59 p.st (vanaf 5 st).jpg",
        "Blinschik (gevulde pancake met zoete kaas of gehakt) - €2.50 p.st (vanaf 5 st).jpg"
    ],
    "04-Hoofdgerechten": [
        "Rijst met Rundvlees en Gedroogd Fruit - €10.99.jpg",
        "Gegrilde Kipfilet - €5.80.jpg",
        "Sperziebonen Roerbak - €5.99.jpg",
        "Chicken Wings - €1.50 p.st (vanaf 10 st).jpg",
        "Gevulde Wijnbladeren met Gehakt of Vegetarisch - €1.99 p.st (vanaf 15 st).jpg",
        "Lasagne Originale of Vegetarisch - €6.99 (vanaf 4 pers).jpg",
        "Lule Kebab (spiezen van rund of kipgehakt) met Aardappelpartjes of Rijst - €14.99 (vanaf 3 pers).jpg",
        "Gehaktkoteletten (rundgehakt of kipgehakt) - €3.50 p.st.jpg",
        "Gevulde Koolrolletjes met Gehakt of Vegetarisch - €1.99 p.st (vanaf 15 st).jpg",
        "Lamskotelet met Rijst of Aardappelpartjes - €13.80 p.p (vanaf 3 pers).jpg",
        "Balletjes in Tomatensaus - €5.99 p.p (vanaf 3 pers).jpg",
        "Gegrilde Groenten (champignons, aubergine, courgette, paprika) - €6.50 (vanaf 3 pers).jpg",
        "Rijstschotel met Gedroogd Fruit - €6.50 p.p (vanaf 3 pers).jpg",
        "Drumsticks - €1.99 p.st (vanaf 8 st).jpg",
        "Beyti Kebab (gevuld bladerdeeg met gehakt) - €15.99 p.p (vanaf 3 pers).jpg",
        "Rijst - €2.90 p.p.jpg",
        "Groenten met Balletjes in Tomatensaus - €9.50 (vanaf 3 pers).jpg",
        "Aardappelpartjes - €2.80.jpg",
        "Gevulde Hele Kip met Walnoten, Ui en Kruiden - €23.95.jpg",
        "Rijst met Kip - €10.95 p.p (vanaf 3 pers).jpg",
        "Rijst met Groenten - €6.50.jpg"
    ]
}

import os
import shutil

# Replace with the path to your menu_orig and menu directories
menu_orig_path = "menu_orig"
menu_path = "menu"

# Ensure the menu directory is created
os.makedirs(menu_path, exist_ok=True)

# Iterate through the cleaned_data list
for ((category_orig, items_orig),(category_cleaned, items_cleaned)) in zip(original_data.items(), cleaned_data.items()):
    # # Create a directory for the cleaned category
    category_cleaned_path = os.path.join(menu_path, category_cleaned)
    os.makedirs(category_cleaned_path, exist_ok=True)

    # Assume correspondence in order
    for item_orig, item_cleaned in zip(items_orig, items_cleaned):
        # Copy the image from menu_orig to menu
        item_orig_path = os.path.join(menu_orig_path, category_orig, item_orig)
        item_cleaned_path = os.path.join(category_cleaned_path, item_cleaned)
        shutil.copyfile(item_orig_path, item_cleaned_path)