#!/bin/bash

# Exit the script if any command fails
set -e

# Installation Script for Coq, CoqIDE, Iris (specific branch), and Evaluation of Coq Artifact on Ubuntu

# 1. (Optional) System Update:
# echo "Updating system..."
# sudo apt update
# sudo apt upgrade -y

# 2. Install prerequisites:
# Installing unzip and git
echo "Installing prerequisites..."
sudo apt install -y unzip git

# 3. Install OPAM:
echo "Installing OPAM..."
sudo apt install -y opam
opam init --auto-setup --yes
eval $(opam env)

# To ensure OPAM environment is always set up, append it to the shell startup script.
echo "eval \$(opam env)" >> ~/.bashrc

# 4. Install Coq and CoqIDE via OPAM:
echo "Installing Coq and CoqIDE..."
opam install coq coqide -y

# 5. Install the specific branch of Iris:
echo "Installing specific branch of Iris..."
git clone -b robbert/sbi https://gitlab.mpi-sws.org/iris/iris.git
cd iris
opam pin add -y coq-iris .
cd ..

# 6. Download and Extract Artifact:
echo "Downloading and extracting artifact..."
wget http://julesjacobs.com/papers/dlfactris/artifact.zip
unzip artifact.zip
cd artifact

# 7. Build Artifact:
echo "Building artifact..."
make

echo "Installation and artifact evaluation completed!"
