#!/bin/bash -x

rm -rf $(isabelle getenv ISABELLE_OUTPUT | cut -d= -f2)
