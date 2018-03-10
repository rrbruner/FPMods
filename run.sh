#!/bin/sh

cd /home/sverre/sage/
./sage -tp 4 ./src/sage/modules/finitely_presented_over_the_steenrod_algebra/resolutions.py
./sage -tp 4 ./src/sage/modules/finitely_presented_over_the_steenrod_algebra/module.py ./src/sage/modules/finitely_presented_over_the_steenrod_algebra/element.py ./src/sage/modules/finitely_presented_over_the_steenrod_algebra/morphism.py ./src/sage/modules/finitely_presented_over_the_steenrod_algebra/homspace.py

