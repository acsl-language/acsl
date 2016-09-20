You are very welcome to contribute to ACSL evolution, from fixing typos in
the current manual to propose clarifications on the semantics of existing
features to introduce new extensions to the language

# How to proceed

There are essentially two main ways to introduce changes in ACSL, which can be
used together or separately:

1. Open a new issue on github (after having verified that no similar issue
   already exist)
1. Fork the repository, make your proposed changes and open a pull-request.

In both cases, please choose an appropriate label (`typo`,
`clarification-request`, `syntax-change`, `semantics-change`, `feature-wish`)
for the intended changes.

Simple changes (e.g. typo or minor rewording) can be directly dealt with in a
pull request. For a more intrusive proposal, such a the introduction of a new
feature, it would be better to start the discussion on an issue, and make the
pull request once a rough consensus has emerged.

# Contribution style

Here are a few guidelines on how to write a good pull-request, especially
for semantics changes or feature wish:

- Each feature should be supported by examples. Any construct that is not
illustrated by an example won't be taken into account.
- Whenever it makes sense, use constructs from JML or C-like languages
(C++, C#, Rust, ...). In particular any divergence from JML should be justified
by the differences between C and Java.
