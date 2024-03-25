FROM ubuntu:focal as build
SHELL ["/bin/bash", "-c"]

# Utilities
RUN apt-get -y update
RUN apt-get install -y git
RUN apt-get install -y make
RUN apt-get install -y wget

# C
RUN apt-get install -y clang

# Rust
RUN apt-get install -y rustc
RUN apt-get install -y cargo

# Dafny
RUN DEBIAN_FRONTEND=noninteractive \
    apt-get install -y dafny

# Coin CBC
RUN apt-get install -y coinor-cbc
RUN apt-get install -y coinor-libcbc-dev

# JRE
RUN DEBIAN_FRONTEND=noninteractive \
    apt-get install -y openjdk-8-jdk
ENV JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64/

# Daikon dependencies
RUN apt-get install -y autotools-dev
RUN apt-get install -y automake
RUN apt-get install -y binutils-dev
RUN apt-get install -y zlib1g-dev
# Daikon
RUN wget http://plse.cs.washington.edu/daikon/download/daikon-5.8.18.tar.gz
RUN tar zxf daikon-5.8.18.tar.gz
ENV DAIKONDIR="/daikon-5.8.18"
RUN source $DAIKONDIR/scripts/daikon.bashrc
RUN make -C $DAIKONDIR kvasir
ENV PATH="$PATH:$DAIKONDIR/scripts"

# Fetch and build KestRel.
RUN git clone https://github.com/rcdickerson/kestrel.git
WORKDIR kestrel
RUN cargo build
