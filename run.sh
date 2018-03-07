#!/bin/sh

cd /home/sverre/sage/
./sage -tp 4 ./src/sage/modules/fpmods/resolutions.py
./sage -tp 4 ./src/sage/modules/fpmods/fpmods.py ./src/sage/modules/fpmods/fpmod_element.py ./src/sage/modules/fpmods/fpmod_morphism.py ./src/sage/modules/fpmods/fpmod_homspace.py

