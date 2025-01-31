#
# Runner for powdr github actions.
# We don't automate runner token generation yet. This image should be used as follows:
# - generate a runner token in github (valid for ~1h)
# - build the docker image passing the token as argument:
#   docker buildx build -t github-runner --build-arg TOKEN=THE_GENERATED_TOKEN .
# - this will create an image already registered it with github
# - the container will start the runner (./run.sh) by default.

# this base image was taken from the Dockerfile in the github runner repo
FROM mcr.microsoft.com/dotnet/runtime-deps:6.0-jammy AS build

ARG RUNNER_VERSION=2.319.1

RUN apt-get update && apt install -y curl \
    sudo \
    libicu70 \
    liblttng-ust1 \
    libkrb5-3 \
    zlib1g \
    libssl3 \
    git \
    build-essential \
    clang-15 \
    nlohmann-json3-dev \
    libpqxx-dev \
    nasm \
    libgmp-dev \
    uuid-dev \
    zstd

RUN adduser --disabled-password --uid 1001 runner \
    && usermod -aG sudo runner \
    && echo "%sudo   ALL=(ALL:ALL) NOPASSWD:ALL" > /etc/sudoers \
    && echo "Defaults env_keep += \"DEBIAN_FRONTEND\"" >> /etc/sudoers

USER runner

WORKDIR /home/runner

RUN curl -f -L -o runner.tar.gz https://github.com/actions/runner/releases/download/v${RUNNER_VERSION}/actions-runner-linux-x64-${RUNNER_VERSION}.tar.gz \
    && tar xzf ./runner.tar.gz \
    && rm runner.tar.gz

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s - -y

ARG TOKEN
RUN test -n "$TOKEN" || (echo "must set github runner TOKEN: --build-arg TOKEN=XXX" && false)

RUN ./config.sh --name arch-server --work work --replace --url https://github.com/powdr-labs/powdr --token ${TOKEN}

# anything that should be in the PATH of the runner must be setup here
ENV PATH="/home/runner/.cargo/bin:$PATH"

CMD ["./run.sh"]
