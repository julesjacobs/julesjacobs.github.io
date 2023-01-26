from PIL import Image, ImageOps
import glob
import os

os.chdir("photos")

imgs = sorted(glob.glob("*.jpg"))

for imgfile in imgs:
  print(imgfile)
  if not os.path.isfile('thumbnails/'+imgfile):
    img = ImageOps.exif_transpose(Image.open(imgfile))
    (h,w) = img.size
    if h > w:
      wr = 500
      hr = round((h * 500)/w)
    else:
      hr = 500
      wr = round((w * 500)/h)
    print((hr,wr))
    thumb = img.resize((hr,wr), Image.LANCZOS)
    # img.thumbnail((400, 400))
    thumb.save('thumbnails/'+imgfile)

template = """
<!DOCTYPE html>
<html lang="en">
  <style>
    #photos {
      display: grid;
      grid-gap: 10px;
      grid-template-columns: repeat(auto-fit, minmax(250px, 1fr));
      grid-auto-rows: 250px;
      grid-auto-flow: dense;
    }
    #photos img {
      object-fit: cover;
      width: 100%%;
      height: 100%%;
    }
  </style>
  <body>
    <div id="photos">
%s
    </div>
  </body>
  <script>
    var imgs = document.getElementsByTagName("img");
    console.log(imgs);
    for(var i=0; i<imgs.length; i++){
      var parent = imgs[i].parentElement;
      parent.innerHtml = '<a href="test.html">' + imgs[i].innerHTML + '</a>';
    }
  </script>
</html>
"""

imghtmls = []
for imgfile in imgs:
  imghtmls.append("""      <a href="%s"><img src="thumbnails/%s" /></a>""" % (imgfile, imgfile))

out = template % "\n".join(imghtmls)
print(out)

open("index.html", "w").write(out)

