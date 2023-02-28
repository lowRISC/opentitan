import puppeteer from 'puppeteer';

export async function ssr(url) {
    const browserOptions = process.argv[2] !== "--debug" ? {
        headless: true,
    } : {
        headless: false,
        devtools: true,
        defaultViewport: { width: 900, height: 600 },
    };

    try {
        const browser = await puppeteer.launch({
            ...browserOptions,
            args: [
                "--no-sandbox",
                "--disable-setuid-sandbox",
                "--disable-web-security",
            ],
        });
        const page = await browser.newPage();
        await page.goto(url, { waitUntil: "networkidle0" });

        await page.evaluate("window.hydrated");

        const head = await page.$eval("head", (e) => e.innerHTML);
        let body = await page.$eval("body", (e) => e.innerHTML);

        body = body.replace(/<(\/)?lowrisc-\w+/g, "<$1div");
        body = body.replace(/<<<HOSTNAME>>>/g, process.env.URL_ROOT || "https://docs.opentitan.org");

        if (browserOptions.headless) {
            await browser.close();
        }

        return `${head}${body}`;
    } catch (error) {
        console.error('SSR Error', error);
        return 'Error while hydrating the page.';
    }
}

const url = new URL("./src/earlgrey.html", import.meta.url);

console.log(await ssr(url.href));
