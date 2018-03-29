# Installation

### Welcome to the docker setup for the verify environment.

To install docker execute the following commands. Follow the instructions outlined [here](https://store.docker.com/editions/community/docker-ce-server-ubuntu).

Once installation is completed follow the instructions [here](https://docs.docker.com/engine/installation/linux/linux-postinstall) to remove the need for sudo.

A number of scripts have been included along with the Dockerfile.

#### Dockerfile
- The Dockerfile describes the base system, in our case it's Ubuntu 16.04. The Dockerfile describes the necessary installation steps to get from a default Ubuntu system to one capable of building the codebase and tools. The standard user is called verify.

#### Scripts
- The build script builds the Dockerfile for your system. It downloads the base and then proceeds to add all the libraries to the image. Every branch will have it's own Dockerfile, merging back in libraries into the master Dockerfile, all of this is done through git of course.

- The run script is reasonably involed. The start related to getting X11 working. The run command creates an interative (-it) session. The $CODE_DIR is mounted at /home/verify/code (-v $CODE_DIR:/home/verify/code), this is a host directory so any changes made to the code here are persistant. The rest of the parameters are to do with hardware acceleration for opengl support for our tools.

- The clean script kills any container (instances of images) that has since exited and deletes any excess images.

- The full clean script kills all containers and all images.
