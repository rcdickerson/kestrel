FROM ubuntu:noble AS build
SHELL ["/bin/bash", "-c"]
#buildpack-deps:jammy-scm

# Utilities
RUN apt-get -y update
RUN apt-get install -yqq git make wget curl unzip

# C
RUN apt-get install -yqq clang

# Rust
RUN curl https://sh.rustup.rs -sSf | bash -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

# Dafny
RUN apt-get install -yqq dotnet-sdk-8.0
RUN wget https://github.com/dafny-lang/dafny/releases/download/v4.9.1/dafny-4.9.1-x64-ubuntu-20.04.zip
RUN unzip dafny-4.9.1-x64-ubuntu-20.04.zip
ENV PATH="/dafny:${PATH}"

# Java
RUN DEBIAN_FRONTEND=noninteractive \
    apt-get install -y openjdk-8-jdk
ENV JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64/

# Python
RUN apt-get install -yqq python3 pip

# Daikon
RUN apt-get install -y autotools-dev automake binutils-dev zlib1g-dev
RUN wget http://plse.cs.washington.edu/daikon/download/daikon-5.8.18.tar.gz
RUN tar zxf daikon-5.8.18.tar.gz
ENV DAIKONDIR="/daikon-5.8.18"
RUN source $DAIKONDIR/scripts/daikon.bashrc
RUN make -C $DAIKONDIR kvasir
ENV PATH="$PATH:$DAIKONDIR/scripts"

# Seahorn
# ---- Modified from Seahorn's Dockerfiles ----
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get install -yqq software-properties-common && \
    apt-get update && \
    apt-get upgrade -yqq && \
    apt-get install -yqq cmake cmake-data unzip \
      zlib1g-dev \
      ninja-build libgraphviz-dev \
      libgmp-dev libmpfr-dev \
      libboost1.74-dev \
      python3-pip \
      less vim \
      gcc-multilib \
      sudo \
      graphviz libgraphviz-dev python3-pygraphviz \
      lcov gcovr rsync \
      clang-14 lldb-14 lld-14 clang-format-14
RUN apt-get install -yqq python3-networkx
RUN pip3 install lit OutputCheck --break-system-packages
RUN apt-get install -yqq libpolly-14-dev

WORKDIR /tmp
RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.9/z3-4.8.9-x64-ubuntu-16.04.zip && \
  unzip z3-4.8.9-x64-ubuntu-16.04.zip && \
  mv z3-4.8.9-x64-ubuntu-16.04 /opt/z3-4.8.9

RUN curl -sSOL https://yices.csl.sri.com/releases/2.6.1/yices-2.6.1-x86_64-pc-linux-gnu-static-gmp.tar.gz && \
  tar xf yices-2.6.1-x86_64-pc-linux-gnu-static-gmp.tar.gz && \
  cd /tmp/yices-2.6.1/ && \
  ./install-yices /opt/yices-2.6.1

WORKDIR /
RUN git clone https://github.com/seahorn/seahorn.git --depth 1 --branch dev14 --single-branch
RUN rm -rf /seahorn/build /seahorn/debug /seahorn/release && \
  mkdir /seahorn/build && \
  rm -rf /seahorn/clam /seahorn/sea-dsa /seahorn/llvm-seahorn
WORKDIR /seahorn/build
ARG BUILD_TYPE=RelWithDebInfo
RUN cmake .. -GNinja \
  -DCMAKE_BUILD_TYPE=${BUILD_TYPE} \
  -DZ3_ROOT=/opt/z3-4.8.9 \
  -DYICES2_HOME=/opt/yices-2.6.1 \
  -DCMAKE_INSTALL_PREFIX=run \
  -DCMAKE_CXX_COMPILER=clang++-14 \
  -DCMAKE_C_COMPILER=clang-14 \
  -DSEA_ENABLE_LLD=ON \
  -DCPACK_GENERATOR="TGZ" \
  -DCMAKE_EXPORT_COMPILE_COMMANDS=ON && \
  cmake --build . --target extra  && cmake .. && \
  cmake --build . --target crab  && cmake .. && \
  cmake --build . --target install && \
  cmake --build . --target units_z3 && \
  cmake --build . --target units_yices2 && \
  cmake --build . --target test_type_checker && \
  cmake --build . --target test_hex_dump && \
  cmake --build . --target package && \
  units/units_z3 && \
  units/units_yices2

ENV PATH="/seahorn/build/run/bin:$PATH"
# -----------------------------------------

# Fetch and build KestRel.
WORKDIR /
RUN apt install python3-tqdm # Needed for experiment scripts.
RUN echo "2"
RUN git clone https://github.com/rcdickerson/kestrel.git --depth 1
WORKDIR /kestrel
RUN cargo build --release
