# Collaboration

- Discussions of features and bugs should take place in [**GitHub Issues**](https://github.com/REPROSEC/dolev-yao-star-extrinsic/issues). This also has the advantage that we can reference the specific issue in meetings.
- Everybody should **create tasks** in the [GitHub Project](https://github.com/orgs/REPROSEC/projects/1) for their work and assign the tasks to themselves.
    - You can also create tasks from Issues and vice versa
- Every change to DY* has to be developed in a separate branch
- If a feature is ready to be merged into the main branch, you **must create a pull request**, and at least one person must review the code changes.
    - PRs are an essential process to guarantee the code quality of DY*.

# Protocol Analysis

- Protocol analysis should take place in a **separate repository** that can either be public or private.
    - You can integrate DY* and Comparse by either using git submodules (preferred solution) or by referencing folders on your system.
- An **example project** will show how to model a protocol in another repository sometime in the future, and it will be linked here.
- For paper publication, you can either pack all the dependencies into one repository or use git submodules to reference a specific git commit in the public DY* and Comparse repositories.