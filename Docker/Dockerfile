FROM ubuntu:16.04
RUN rm /bin/sh && ln -s /bin/bash /bin/sh

RUN rm /etc/apt/apt.conf.d/docker-clean

RUN apt-get update -y --fix-missing
RUN apt-get dist-upgrade -y

# Libraries
RUN apt-get update -y && \
    apt-get install -y build-essential git sudo vim gedit

# Create a user
ENV USERNAME verify
RUN useradd $USERNAME -m
RUN export uid=$(id $USERNAME -u) gid=$(id $USERNAME -g) && \
    echo "$USERNAME:x:${uid}:${gid}:$USERNAME,,,:/home/$USERNAME:/bin/bash" >> /etc/passwd && \
    echo "$USERNAME:x:${uid}:" >> /etc/group && \
    echo "$USERNAME ALL=(ALL) NOPASSWD: ALL" > /etc/sudoers && \
    chown ${uid}:${gid} -R /home/$USERNAME

USER $USERNAME
WORKDIR /home/$USERNAME

# Auto complete
RUN sudo apt-get install -y bash-completion fish

# Boogie and Dafny depedencies
RUN sudo apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv-keys 3FA7E0328081BFF6A14DA29AA6A19B38D3D831EF && \
    echo "deb http://download.mono-project.com/repo/ubuntu xenial main" | sudo tee /etc/apt/sources.list.d/mono-official.list && \
    sudo apt-get update
RUN sudo apt-get install -y mono-devel g++ wget

# "Install" Boogie
RUN git clone https://github.com/boogie-org/boogie && \
    cd boogie && \
    wget https://nuget.org/nuget.exe && \
    mono ./nuget.exe restore Source/Boogie.sln && \
    xbuild Source/Boogie.sln

# "Install" Dafny
RUN git clone https://github.com/Microsoft/dafny.git && \
   cd dafny && \
   #git checkout e2237e2afaddc9fb24af7f8ba1f4b257554dbd5b && \
   msbuild Source/Dafny.sln && \
   chmod +x Binaries/Dafny.exe && \
   chmod +x Binaries/DafnyServer.exe

# "Install" Z3
RUN git clone https://github.com/Z3Prover/z3.git && \
   cd z3 && \
   python scripts/mk_make.py && \
   cd build && \
   make -j `grep -c '^processor' /proc/cpuinfo`

# Copy Z3 to
RUN mkdir dafny/Binaries/z3 && \
   mkdir dafny/Binaries/z3/bin && \
   cp z3/build/z3 dafny/Binaries/z3/bin/ && \
   cp z3/build/z3 boogie/Binaries/

# Why3 dependencies
RUN sudo apt-get install -y autoconf ocaml menhir

# Why3
RUN git clone https://scm.gforge.inria.fr/anonscm/git/why3/why3.git && \
   cd why3 && \
   autoconf && \
   automake --add-missing || true && \
   ./configure && \
   make && \
   sudo make install && \
   make byte && \
   sudo make install-lib

# For apt-add-repository
RUN sudo apt-get install -y software-properties-common apt-transport-https

# SBT repos
RUN echo "deb https://dl.bintray.com/sbt/debian /" | sudo tee -a /etc/apt/sources.list.d/sbt.list
RUN sudo apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv 2EE0EA64E40A89B84B2DF73499E82A75642AC823
RUN sudo apt-get update

# Add Java repos
RUN sudo apt-add-repository -y ppa:openjdk-r/ppa && \
    sudo apt-get update -y

# Vercors depedencies
RUN sudo apt-get install -y openjdk-8-jdk openjdk-8-jre ant libcommons-math-java sbt

# Vercors
RUN git clone https://github.com/utwente-fmt/vercors.git && \
    cd vercors && \
    export JAVA_TOOL_OPTIONS=-Dfile.encoding=UTF8 && \
    ./unix/bin/vct-ant

# Install visual studio code dependencies
RUN sudo apt-get install -y curl

# Install visual studio code, symlink at the end to make plugins and extensions persistent
RUN curl https://packages.microsoft.com/keys/microsoft.asc | gpg --dearmor > microsoft.gpg && \
    sudo mv microsoft.gpg /etc/apt/trusted.gpg.d/microsoft.gpg && \
    sudo sh -c 'echo "deb [arch=amd64] https://packages.microsoft.com/repos/vscode stable main" > /etc/apt/sources.list.d/vscode.list' && \
    sudo apt-get update && \
    sudo apt-get install -y code && \
    ln -s $HOME/code/.vscode && \
    ln -s $HOME/code/Code .config/Code

# Graphics
RUN sudo apt-get install -y libxss1 wget libnotify4 libgconf-2-4 libnss3 libgtk2.0-0 libxss1 libgconf-2-4 libasound2 libxtst6 libcanberra-gtk-dev libgl1-mesa-glx libgl1-mesa-dri

CMD ["/bin/bash"]
