#!/bin/bash

XSOCK=/tmp/.X11-unix
XAUTH=/tmp/.docker.xauth
touch $XAUTH
xauth nlist $DISPLAY | sed -e 's/^..../ffff/' | xauth -f $XAUTH nmerge -
# FILL ME IN WITH CODE DIR, EG. CODE_DIR=~/work/verification/code
CODE_DIR=
mkdir -p $CODE_DIR/.vscode
mkdir -p $CODE_DIR/Code
docker run -it -v $XSOCK:$XSOCK:rw --privileged -v $XAUTH:$XAUTH:rw -e QT_X11_NO_MITSHM=1 -e "DISPLAY=unix:0.0" -e XAUTHORITY=$XAUTH -v $CODE_DIR:/home/verify/code --rm verify-env
