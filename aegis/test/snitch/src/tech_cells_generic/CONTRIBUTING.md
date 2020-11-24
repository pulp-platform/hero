# Contributing to Repositories

## Branches, Pull Requests, and Tags

Never push to master if you are not the repository owner.

Contributions are very welcome nonetheless: create a new branch (starting from `master`) for your work (no matter how small) and use that branch to develop and test your feature or bugfix in the scope of your project.  If you ever intend your work to become mainline (and we highly recommend you do!), create a Pull Request to discuss your work with the repository owner. We recommend you do so early, as soon as the central parts of your contribution work, to ensure that you are not doing work in vain.  Use the WIP tag if your work is not yet finalized.

Never push a release tag (i.e., a tag starting with `v`) if you are not the owner of a repository or had a release PR approved by the owner.

## Commits

Git commits are how you communicate and contribute your work, so their quality is important.  However, your main objective is to get work done, not to create perfect commits in the first place.  To combine these aspects, we suggest a three phase approach:

1. While working on your own branch: commit early, commit often, commit dirty.  The only person that has to understand your commits are you yourself (and close collaborators if you are triaging a feature or bug in a team).  Try to commit atomic pieces of work such that you can develop rapidly, explore variants, and roll back defective changes.

2. Before opening a PR: Rebase your branch to create meaningful commits (see below), squashing multiple phase 1 commits that jointly implement a feature or bugfix and removing phase 1 commits that are no longer relevant. Ask yourself "How would I want to review my work?" and restructure accordingly.

3. While your PR is being reviewed, you might be asked to make changes to your commits (use fixup commits for this) or add more commits.  Depending on the scope of your PR, this might take a few iterations.  Once your PR is agreed and before it gets merged, you or the repository owner does a final rebase to clean fixups and remove conflicts with the master branch.

When your commits are to be read by others, write descriptive git commit messages.  Separate subject from body with a blank line.  Limit the subject line to 50 characters.  Read [this short article](https://tbaggery.com/2008/04/19/a-note-about-git-commit-messages.html) for more detailed guidelines.

## Contributing Hardware Modules

For common functionality (e.g., a FIFO, clock gating cells, or clock generators for simulation) try to use existing modules in the repositories `common_cells`, `tech_cells_generic`, and `common_verification` as much as possible.  If no module exists that fulfills your needs but it might be a useful common module, open a PR in one of those repositories.  If an existing module almost fulfills your purpose, suggest an extension by making a PR in one of those repositories.

Before creating a repository for a new HW module, try to fit it into an existing repository.  This makes it easier for people to find and use your work and for maintainers of a topic (e.g., AXI, uDMA, ...) to keep the work of the organization aligned.  If you think you have to create a new repository, propose it to an organization owner.

Follow [our style guideline](https://github.com/pulp-platform/style-guidelines).  If a source file already has a consistent style and you make only minor changes, keep the style of the file consistent.
