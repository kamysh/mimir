# Upgrade the widget dependency

This project pins the `widget` library in `deps.lock`, and `python build.py`
currently passes. We want to be on the newest widget available.

Update the project so it uses the newest widget version while `python build.py`
still exits 0. You may edit `deps.lock` and `app.py`. Do **not** edit anything
under `widgets/`.
