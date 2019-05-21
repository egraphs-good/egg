#!/usr/bin/env bash

set -ev

cargo web deploy

rsync -az ../target/deploy/ mwillsey.com:/var/www/stuff/egg/
