set -euxo pipefail

main() {
    cargo check --features "FLI$FLI" --target $T

    if [ $T = x86_64-unknown-linux-gnu ]; then
        cargo test --features "FLI$FLI"
        cargo test --features "FLI$FLI" --release
    fi
}

# fake Travis variables to be able to run this on a local machine
if [ -z ${TRAVIS_BRANCH-} ]; then
    TRAVIS_BRANCH=auto
fi

if [ -z ${TRAVIS_PULL_REQUEST-} ]; then
    TRAVIS_PULL_REQUEST=false
fi

if [ -z ${TRAVIS_RUST_VERSION-} ]; then
    case $(rustc -V) in
        *nightly*)
            TRAVIS_RUST_VERSION=nightly
            ;;
        *beta*)
            TRAVIS_RUST_VERSION=beta
            ;;
        *)
            TRAVIS_RUST_VERSION=stable
            ;;
    esac
fi

if [ -z ${T-} ]; then
    T=$(rustc -Vv | grep host | cut -d ' ' -f2)
fi

if [ -z ${FLI-} ]; then
    FLI=8
fi

if [ $TRAVIS_BRANCH != master ] || [ $TRAVIS_PULL_REQUEST != false ]; then
    main
fi
