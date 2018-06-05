#!/bin/bash
gs \
 -sOutputFile=output.pdf \
 -sDEVICE=pdfwrite \
 -sColorConversionStrategy=Gray \
 -dProcessColorModel=/DeviceGray \
 -dCompatibilityLevel=1.4 \
 -dAutoRotatePages=/None \
 -dNOPAUSE \
 -dBATCH \
 $1
