const CopyWebpackPlugin = require("copy-webpack-plugin");
const path = require('path');

module.exports = {
    entry: "./bootstrap.js",
    output: {
        path: path.resolve(__dirname, "dist"),
        filename: "bootstrap.js",
    },
    mode: "development",
    plugins: [
        new CopyWebpackPlugin(
            [
                {
                    from: '.nojekyll',
                    to: '.nojekyll',
                    toType: 'file',
                },
                {
                    from: 'index.html',
                    to: 'index.html',
                },
                {
                    from: 'node_modules/xterm/css/xterm.css',
                    to: 'node_modules/xterm/css/xterm.css',
                },
                {
                    from: 'style.css',
                    to: 'style.css',
                },
            ],
        ),
    ],
};
