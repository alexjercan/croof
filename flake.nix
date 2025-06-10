{
  description = "A basic flake for my Rust Project";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
  }: (
    flake-utils.lib.eachDefaultSystem
    (system: let
      pkgs = import nixpkgs {
        inherit system;

        config = {
          allowUnfree = true;
        };
      };
      manifest = (pkgs.lib.importTOML ./Cargo.toml).package;
    in {
      packages.default = pkgs.rustPlatform.buildRustPackage {
        pname = manifest.name;
        version = manifest.version;
        cargoLock.lockFile = ./Cargo.lock;
        src = pkgs.lib.cleanSource ./.;
      };

      packages.checker = pkgs.writeShellApplication {
        name = "checker";
        text =
          /*
          bash
          */
          ''
            set +o errexit
            set +o pipefail

            MAIN=target/release/${manifest.name}
            TESTS_DIR=tests
            TOTAL_TESTS=0
            PASSED_TESTS=0
            EXT=croof

            ARG1="all"
            VERBOSE=0

            analyzer() {
                if [ "$#" -ne 3 ]; then
                    echo "Usage: analyzer <tests_dir> <exec_arg> <verbose>"
                    exit 1
                fi

                tests_dir=$TESTS_DIR/$1
                exec_arg=$2
                verbose=$3

                echo "Running tests for $1"

                passed=0
                total=0
                for file_path in "$tests_dir"/*."$EXT"; do
                    total=$((total + 1))

                    ref_path="$tests_dir"/$(basename "$file_path" ."$EXT").ref

                    file_name=$(basename "$file_path")
                    echo -en "Testing $file_name ... "

                    if [ ! -f "$ref_path" ]; then
                        echo "TODO: Fill in the reference output" > "$ref_path"
                    fi

                    diff_output=$(./"$MAIN" "$exec_arg" "$file_path" 2>&1 | diff - "$ref_path")
                    test_status=$?
                    if [ "$test_status" -eq 0 ]; then
                        echo -e "\e[32mPASSED\e[0m"
                        passed=$((passed + 1))
                    else
                        echo -e "\e[31mFAILED\e[0m"
                        if [ -n "$diff_output" ] && [ "$verbose" -eq 1 ]; then
                            echo "$diff_output"
                        fi
                    fi
                done

                echo "Passed $passed/$total tests"
                TOTAL_TESTS=$((TOTAL_TESTS + total))
                PASSED_TESTS=$((PASSED_TESTS + passed))
            }

            usage() {
                echo "Usage: $0 [--all | --lexer | --parser | --typecheck] [--main <main>] [-h | --help]"
                echo
                echo "Options:"
                echo "  --all           Enable 'all' mode."
                echo "  --lexer         Enable 'lexer' mode."
                echo "  --parser        Enable 'parser' mode."
                echo "  --typecheck     Enable 'typecheck' mode."
                echo "  -v, --verbose   Show more details in case of errors."
                echo "  --main <main>   Switch to a different main. Default is 'main'"
                echo "  -h, --help      Show this help message and exit."
            }

            main() {
                ${pkgs.cargo}/bin/cargo build --release || exit 1

                while [[ $# -gt 0 ]]; do
                    case "$1" in
                        --all)
                            ARG1="all"
                            shift
                            ;;
                        --lexer)
                            ARG1="lexer"
                            shift
                            ;;
                        --parser)
                            ARG1="parser"
                            shift
                            ;;
                        --typecheck)
                            ARG1="typecheck"
                            shift
                            ;;
                        -v|--verbose)
                            VERBOSE=1
                            shift
                            ;;
                        --main)
                            if [ -z "$2" ]; then
                                echo "$1"
                                echo "$2"
                                usage
                                exit 1
                            fi
                            MAIN="$2"
                            shift
                            shift
                            ;;
                        -h|--help)
                            usage
                            exit 0
                            ;;
                        *)
                            usage
                            exit 1
                            ;;
                    esac
                done

                if [[ "$ARG1" == "lexer" || "$ARG1" == "all" ]]; then
                    echo -e "\e[33mTesting the lexical analyzer\e[0m"
                    analyzer "01-lexer" "--lexer" "$VERBOSE"
                fi

                if [[ "$ARG1" == "parser" || "$ARG1" == "all" ]]; then
                    echo -e "\e[33mTesting the parser\e[0m"
                    analyzer "02-parser" "--parser" "$VERBOSE"
                fi

                if [[ "$ARG1" == "typecheck" || "$ARG1" == "all" ]]; then
                    echo -e "\e[33mTesting the typechecker\e[0m"
                    analyzer "03-typecheck" "--typecheck" "$VERBOSE"
                fi

                if [ $PASSED_TESTS -eq $TOTAL_TESTS ]; then
                    echo -e "\e[32mAll tests passed\e[0m"
                    exit 0
                else
                    echo -e "\e[31mSome tests failed\e[0m"
                    exit 1
                fi
            }

            if [[ $# -eq 1 && ($1 == "--help" || $1 == "-h") ]]; then
                usage
                exit 0
            fi

            main "$@"
          '';
      };

      devShells.default = pkgs.mkShell rec {
        nativeBuildInputs = with pkgs; [
          cargo
          rustc
          rustfmt
          clippy
        ];

        buildInputs = with pkgs; [];

        LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath buildInputs;

        RUST_BACKTRACE = 1;

        RUST_SRC_PATH = "${pkgs.rust.packages.stable.rustPlatform.rustLibSrc}";
      };
    })
  );
}
