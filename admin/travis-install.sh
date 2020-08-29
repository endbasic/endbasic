#! /bin/sh
# EndBASIC
# Copyright 2020 Julio Merino
#
# Licensed under the Apache License, Version 2.0 (the "License"); you may not
# use this file except in compliance with the License.  You may obtain a copy
# of the License at:
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
# License for the specific language governing permissions and limitations
# under the License.

set -eux

if [ "${DO-unset}" = unset ]; then
    echo "DO must be set in the environment" 1>&2
    exit 1
fi
case "${DO}" in
    lint)
        rustup component add clippy
        rustup component add rustfmt
        ;;

    web)
        curl -o- \
            https://raw.githubusercontent.com/nvm-sh/nvm/v0.35.3/install.sh \
            | bash

        export NVM_DIR="${HOME}/.nvm"
        [ -s "${NVM_DIR}/nvm.sh" ] && . "${NVM_DIR}/nvm.sh"
        nvm install --lts

        curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh
        ;;

    *)
        # Nothing else to do.
        ;;
esac
