FROM debian

# Install Rust and Cargo
# TODO: make this architecture agnostic
RUN apt-get update && apt-get install -yy sudo wget 
RUN wget https://static.rust-lang.org/dist/rust-nightly-x86_64-unknown-linux-gnu.tar.gz
RUN tar xvf rust-nightly-x86_64-unknown-linux-gnu.tar.gz
RUN cd rust-nightly-x86_64-unknown-linux-gnu && ./install.sh


# Install libsnark dependencies
# g++ (for building libsnark)
# libgmp-dev (for bigint math)
RUN apt-get update && apt-get install -yy g++ libgmp-dev

# Include this directory in the built image

ADD . /bellman