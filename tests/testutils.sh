#!/bin/sh

basicTest() {
  idris2 --quiet --console-width 0 --no-color -p semantic-reflection "$@" | sed 's/Main> //' | sed 's/\(Main> \)\+/\n/'

  rm -rf build
}
