{
  description = "C++ Development Environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = inputs@{ flake-parts, ... }: 
    flake-parts.lib.mkFlake {inherit inputs;} {

    systems = [
      "x86_64-linux" "aarch64_linux" "aarch64_darwin" "x86_64-darwin"
    ];
    perSystem = {config, self', inputs', pkgs, system, ...}: {
      devShells.default = pkgs.mkShell {
        packages = with pkgs; [
	  #dev stuff
	  git
	  gcc
	  cmake
	  gnumake
	  
	  #build stuff for compiling postgres
	  #icu is missing due to installation issues
	  bison
	  flex
	  readline
	  zlib
	  antlr
	  zulu23
	];
      };
    };
  };
}

